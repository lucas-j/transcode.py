#!/usr/bin/env python
# -*- coding: utf-8 -*-

'''
This program uses a MythTV database or WTV recording to transcode
recorded TV programs to MPEG-4 video using the H.264 and AAC codecs, cutting
the video at certain commercial points selected by the user within MythTV's
frontend or by an automatic commercial flagger, complete with SRT subtitles
extracted from the embedded VBI closed-caption data, and iTunes-style
metadata about the program, if it can be found.

In short, this program calls a bunch of programs to convert a file like
1041_20100523000000.mpg or Program Name_ABC_2010_05_23_00_00_00.wtv into a
file like /srv/video/Program Name/Program Name - Episode Name.mp4,
including captions, file tags, chapters, and with commercials removed.

This program has been tested on Windows, Linux and FreeBSD, and can optionally
transcode from remote sources - e.g., mythbackend / MySQL running on a
different computer, or WTV source files from a remote SMB share / HomeGroup.

Requirements:
- FFmpeg
- x264 (ffmpeg will be called with -vcodec libx264)
- neroAacEnc (http://www.nero.com/enu/technologies-aac-codec.html)
- Project-X and a suitable JVM (http://project-x.sourceforge.net)
- remuxTool.jar for WTV (http://babgvant.com/downloads/dburckh/remuxTool.jar)
- MP4Box (http://gpac.sourceforge.net)
- ccextractor (http://ccextractor.sourceforge.net)
- AtomicParsley (https://bitbucket.org/wez/atomicparsley)
- Python 2.6+ (http://www.python.org)
  - lxml (http://lxml.de)
  - mysql-python (http://sourceforge.net/projects/mysql-python)
  - the MythTV Python bindings (if MythTV is not installed already)

Most of these packages can usually be found in various Linux software
repositories or as pre-compiled Windows binaries.

Setup:
- Make sure the above dependencies are installed on your system. Add each
  binary location to your PATH variable if necessary.
- Change the default values within this file, or specify appropriate
  command-line options.

Usage:
  transcode.py %CHANID% %STARTTIME%
  transcode.py /path/to/file.wtv
See transcode.py --help for more details

Notes on format string:
Each of the below tags are replaced with the respective metadata obtained
from MythTV, the WTV file, or Tvdb, if it can be found. Path separators
(slashes) indicate that new directories are to be created if necessary.
  %T - title (name of the show)
  %S - subtilte (name of the episode)
  %R - description (short plot synopsis)
  %C - category (genre of the show)
  %n - episode production code (or %s%e if unavailable)
  %s - season number
  %E - episode number (as reported by Tvdb)
  %e - episode number, padded with zeroes if necessary
  %r - content rating (e.g., TV-G)
  %oy - year of original air date (two digits)
  %oY - year of original air date (full four digits)
  %om - month of original air date (two digits)
  %od - day of original air date (two digits)
  
Special thanks to:
- #MythTV Freenode
- wagnerrp, the maintainer of the Python MythTV bindings
- Project-X team
'''

# Changelog:
# 1.1 - support for multiple audio streams, Comskip
# 1.0 - initial release

# TODO:
# - use a custom exception
# - check for adequate disk space on /tmp and destination partitions
# - generate thumbnail if necessary
# - better genre interpretation for WTV files

# Long-term goals:
# - support for boxed-set TV seasons on DVD
# - metadata / chapter support for as many different players as possible,
#   especially Windows Media Player
# - optionally use Matroska / VP8 as a target format
# - easier access and configuration
# - easier installation: all required programs should be bundled

# Known issues:
# - subtitles seem to be out-of-sync when played with MPlayer, works in vlc
# - subtitle font is sometimes too large on QuickTime / iTunes / iPods

import re, os, sys, math, datetime, subprocess, contextlib, threading
import urllib, tempfile, glob, shutil, codecs, StringIO, time, optparse
import unicodedata, logging, xml.dom.minidom
import MythTV, MythTV.ttvdb.tvdb_api, MythTV.ttvdb.tvdb_exceptions

# --- Change these default values before using this program ---

# directory to store encoded video file
_OUT_DEFAULT = '/srv/video'

# temporary directory to use while encoding
# (if left as None, a temporary directory will be created)
_TMP_DEFAULT = None

# format string for the encoded video filename. some examples:
# '%T/%T - %S' -> 'Show/Show - Episode'
# '%C/%T/%o - %S' -> 'Genre/Show/1x23 - Episode'
# '%oY/%T (%sx%e) - %S' -> '2012/Show (1x23) - Episode'
_FMT_DEFAULT = '%T/%T - %S'

# two-letter language code (ISO 639-2) of the audio track to be obtained
_LANG_DEFAULT = 'en'

# MythTV database host (change this if using MythTV)
_HOST_DEFAULT = '127.0.0.1'

# MySQL database for MythTV (usually 'mythconverg')
_DB_DEFAULT = 'mythconverg'

# MySQL username for MythTV (usually 'mythtv')
_USER_DEFAULT = 'mythtv'

# MySQL password for MythTV (usually 'mythtv')
_PASS_DEFAULT = 'mythtv'

# path to the Project-X JAR file (used for noise cleaning / cutting)
_PROJECTX_DEFAULT = 'project-x/ProjectX.jar'

# path to remuxTool.jar (used for extracting MPEG-2 data from WTV files)
_REMUXTOOL_DEFAULT = 'remuxTool.jar'

def _clean(filename):
    'Removes the file if it exists.'
    try:
        os.remove(filename)
    except OSError:
        pass

def _convert_time(time):
    '''Converts a timestamp string into a datetime object.
    For example, '20100523140000' -> datetime(2010, 5, 23, 14, 0, 0) '''
    time = str(time)
    ret = None
    if len(time) != 14:
        raise ValueError('Invalid timestamp - must be 14 digits long.')
    try:
        ret = datetime.datetime.strptime(time, '%Y%m%d%H%M%S')
    except ValueError:
        raise ValueError('Invalid timestamp.')
    return ret

def _seconds_to_time(sec):
    '''Returns a string representation of the length of time provided.
    For example, 3675.14 -> '01:01:15' '''
    sec = sec
    hours = int(sec / 3600)
    sec -= hours * 3600
    minutes = int(sec / 60)
    sec -= minutes * 60
    return '%02d:%02d:%02d' % (hours, minutes, sec)

def _seconds_to_time_frac(sec):
    '''Returns a string representation of the length of time provided,
    including partial seconds.
    For example, 3675.14 -> '01:01:15.140000' '''
    hours = int(sec / 3600)
    sec -= hours * 3600
    minutes = int(sec / 60)
    sec -= minutes * 60
    return '%02d:%02d:%07.4f' % (hours, minutes, sec)

def _last_name_first(name):
    '''Reverses the order of full names of people, so their last name
    appears first.'''
    names = name.split()
    if len(names) == 0:
        return names
    else:
        return u' '.join((names[-1], ' '.join(names[:-1]))).strip()

def _sanitize(filename, repl = None):
    '''Replaces any invalid characters in the filename with repl. Invalid
    characters include anything from \x00 - \x31, and some other characters
    on Windows. UTF-8 characters are translated loosely to ASCII on systems
    which have no Unicode support. Unix systems are assumed to have Unicode
    support. Note that directory separators (slashes) are allowed as they
    specify that a new directory is to be created.'''
    if repl is None:
        repl = ''
    not_allowed = ''
    if os.name == 'nt':
        not_allowed += '<>:|?*'
    out = ''
    for ch in filename:
        if ch not in not_allowed and ord(ch) >= 32:
            if os.name == 'posix' or os.path.supports_unicode_filenames \
                    or ord(ch) < 127:
                out += ch
            else:
                ch = unicodedata.normalize('NFKD', ch)
                ch = ch.encode('ascii', 'ignore')
                out += ch
        else:
            out += repl
    if os.name == 'nt':
        out = out.replace('"', "'")
        reserved = ['con', 'prn', 'aux', 'nul']
        reserved += ['com%d' % d for d in range(0, 10)]
        reserved += ['lpt%d' % d for d in range(0, 10)]
        for r in reserved:
            regex = re.compile(r, re.IGNORECASE)
            out = regex.sub(repl, out)
    return out

def _cmd(args, cwd = None, expected = 0):
    '''Executes an external command with the given working directory, ignoring
    all output. Raises a RuntimeError exception if the return code of the
    subprocess isn't what is expected.'''
    args = [unicode(arg).encode('utf_8') for arg in args]
    ret = 0
    logging.debug('$ %s' % u' '.join(args))
    proc = subprocess.Popen(args, stdout = subprocess.PIPE,
                            stderr = subprocess.STDOUT, cwd = cwd)
    for line in proc.stdout:
        logging.debug(line.replace('\n', ''))
    ret = proc.wait()
    if ret != 0 and ret != expected:
        raise RuntimeError('Unexpected return code', u' '.join(args), ret)
    return ret

def _ver(args, regex, use_stderr = True):
    '''Executes an external command and searches through the standard output
    (and optionally stderr) for the provided regular expression. Returns the
    first matched group, or None if no matches were found.'''
    ret = None
    with open(os.devnull, 'w') as devnull:
        try:
            stderr = subprocess.STDOUT
            if not use_stderr:
                stderr = devnull
            proc = subprocess.Popen(args, stdout = subprocess.PIPE,
                                    stderr = stderr)
            for line in proc.stdout:
                match = re.search(regex, line)
                if match:
                    ret = match.group(1)
                    break
            for line in proc.stdout:
                pass
            proc.wait()
        except OSError:
            pass
    return ret

def _iso_639_2(lang):
    '''Translates from a two-letter ISO language code (ISO 639-1) to a
    three-letter ISO language code (ISO 639-2).'''
    languages = {'cs' : 'ces', 'da' : 'dan', 'de' : 'deu', 'es' : 'spa',
                 'el' : 'ell', 'en' : 'eng', 'fi' : 'fin', 'fr' : 'fra',
                 'he' : 'heb', 'hr' : 'hrv', 'hu' : 'hun', 'it' : 'ita',
                 'ja' : 'jpn', 'ko' : 'kor', 'nl' : 'nld', 'no' : 'nor',
                 'pl' : 'pol', 'pt' : 'por', 'ru' : 'rus', 'sl' : 'slv',
                 'sv' : 'swe', 'tr' : 'tur', 'zh' : 'zho'}
    if lang in languages.keys():
        return languages[lang]
    else:
        raise ValueError('Invalid language code %s.' % lang)

def _get_options():
    'Uses optparse to obtain command-line options.'
    usage = 'usage: %prog [options] chanid time\n' + \
        '  %prog [options] wtv-file'
    version = '%prog 1.1'
    parser = optparse.OptionParser(usage = usage, version = version,
                                   formatter = optparse.TitledHelpFormatter())
    flopts = optparse.OptionGroup(parser, 'File options')
    flopts.add_option('-o', '--out', dest = 'final_path', metavar = 'PATH',
                      default = _OUT_DEFAULT, help = 'directory to ' +
                      'store encoded video file                    ' +
                      '[default: %default]')
    if _TMP_DEFAULT:
        flopts.add_option('-t', '--tmp', dest = 'tmp', metavar = 'PATH',
                          default = _TMP_DEFAULT, help = 'temporary ' +
                          'directory to be used while transcoding ' +
                          '[default: %default]')
    else:
        flopts.add_option('-t', '--tmp', dest = 'tmp', metavar = 'PATH',
                          help = 'temporary directory to be used while ' +
                          'transcoding [default: %s]' % tempfile.gettempdir())
    flopts.add_option('--format', dest = 'final_format',
                      default = _FMT_DEFAULT, metavar = 'FMT',
                      help = 'format string for the encoded video filename ' +
                      '          [default: %default]')
    flopts.add_option('--replace', dest = 'replace_char', default = '',
                      metavar = 'CHAR', help = 'character to substitute ' +
                      'for invalid filename characters [default: nothing]')
    flopts.add_option('-l', '--lang', dest = 'language',
                      default = _LANG_DEFAULT, metavar = 'LANG',
                      help = 'two-letter language code [default: %default]')
    parser.add_option_group(flopts)
    viopts = optparse.OptionGroup(parser, 'Video encoding options')
    viopts.add_option('-1', '--one-pass', dest = 'two_pass',
                      action = 'store_false', default = False,
                      help = 'one-pass encoding [default]')
    viopts.add_option('-2', '--two-pass', dest = 'two_pass',
                      action = 'store_true', help = 'two-pass encoding')
    viopts.add_option('-p', '--preset', dest = 'preset', metavar = 'PRE',
                      default = None, help = 'ffmpeg x264 preset to use ' +
                      '[default: %default]')
    viopts.add_option('--video-br', dest = 'video_br', metavar = 'BR',
                      type = 'int', default = 1500, help = 'two-pass target ' +
                      'video bitrate (in KB/s) [default: %default]')
    viopts.add_option('--video-crf', dest = 'video_crf', metavar = 'CR',
                      type = 'int', default = 22, help = 'one-pass target ' +
                      'compression ratio (~15-25 is ideal) ' +
                      '[default: %default]')
    viopts.add_option('--ipod', dest = 'ipod', action = 'store_true',
                      default = True, help = 'use iPod Touch compatibility ' +
                      'settings [default]')
    viopts.add_option('--no-ipod', dest = 'ipod', action = 'store_false',
                      help = 'do not use iPod compatibility settings')
    viopts.add_option('--ipod-preset', dest = 'ipod_preset', metavar = 'PRE',
                      default = 'ipod640', help = 'ffmpeg x264 preset to ' +
                      'use for iPod Touch compatibility [default: %default]')
    parser.add_option_group(viopts)
    auopts = optparse.OptionGroup(parser, 'Audio encoding options')
    auopts.add_option('-n', '--nero', dest = 'nero', action = 'store_true',
                      default = True, help = 'use NeroAacEnc (must be ' +
                      'installed) [default]')
    auopts.add_option('-f', '--faac', dest = 'nero', action = 'store_false',
                      help = 'use libfaac (must be linked into ffmpeg)')
    auopts.add_option('--audio-br', dest = 'audio_br', metavar = 'BR',
                      type = 'int', default = 128, help = 'libfaac audio ' +
                      'bitrate (in KB/s) [default: %default]')
    auopts.add_option('--audio-q', dest = 'audio_q', metavar = 'Q',
                      type = 'float', default = 0.3, help = 'neroAacEnc ' +
                      'audio quality ratio [default: %default]')
    parser.add_option_group(auopts)
    mdopts = optparse.OptionGroup(parser, 'Metadata options')
    mdopts.add_option('--rating', dest = 'use_tvdb_rating',
                      action = 'store_true', default = True,
                      help = 'include Tvdb episode rating (1 to 10) ' +
                      'as voted by users [default]')
    mdopts.add_option('--no-rating', dest = 'use_tvdb_rating',
                      action = 'store_false', help = 'do not include Tvdb ' +
                      'episode rating')
    mdopts.add_option('--tvdb-description', dest = 'prefer_tvdb_descriptions',
                      action = 'store_true', default = False,
                      help = 'prefer to use episode description from Tvdb ' +
                      'when available')
    parser.add_option_group(mdopts)
    myopts = optparse.OptionGroup(parser, 'MythTV options')
    myopts.add_option('--host', dest = 'host', metavar = 'IP',
                      default = _HOST_DEFAULT, help = 'MythTV database ' +
                      'host [default: %default]')
    myopts.add_option('--database', dest = 'database', metavar = 'DB',
                      default = _DB_DEFAULT, help = 'MySQL database for ' +
                      'MythTV [default: %default]')
    myopts.add_option('--user', dest = 'user', metavar = 'USER',
                      default = _USER_DEFAULT, help = 'MySQL username for ' +
                      'MythTV [default: %default]')
    myopts.add_option('--password', dest = 'password', metavar = 'PWD',
                      default = _PASS_DEFAULT, help = 'MySQL password for ' +
                      'MythTV [default: %default]')
    myopts.add_option('--pin', dest = 'pin', metavar = 'PIN', type = 'int',
                      default = 0, help = 'MythTV security PIN ' +
                      '[default: 0000]')
    parser.add_option_group(myopts)
    miopts = optparse.OptionGroup(parser, 'Miscellaneous options')
    miopts.add_option('-q', '--quiet', dest = 'quiet', action = 'store_true',
                      default = False, help = 'avoid printing to stdout')
    miopts.add_option('-v', '--verbose', dest = 'verbose',
                      action = 'store_true', default = False,
                      help = 'print command output to stdout')
    miopts.add_option('--thresh', dest = 'thresh', metavar = 'TH',
                      type = 'int', default = 5, help = 'avoid clipping ' +
                      'commercials TH seconds from the beginning or end ' +
                      '[default: %default]')
    miopts.add_option('--project-x', dest = 'projectx', metavar = 'PATH',
                      default = _PROJECTX_DEFAULT, help = 'path to the ' +
                      'Project-X JAR file                              ' +
                      '(used for noise cleaning / cutting)')
    miopts.add_option('--remuxtool', dest = 'remuxtool', metavar = 'PATH',
                      default = _REMUXTOOL_DEFAULT, help = 'path to ' +
                      'remuxTool.jar                                ' +
                      '(used for extracting MPEG-2 data from WTV files)')
    parser.add_option_group(miopts)
    return parser

def _check_args(args, parser):
    'Checks to ensure the positional arguments are valid.'
    if len(args) == 2:
        try:
            ts = _convert_time(args[1])
        except ValueError:
            print 'Error: invalid timestamp.'
            exit(1)
    elif len(args) == 1:
        if not os.path.exists(args[0]):
            print 'Error: file not found.'
            exit(1)
        if not re.search('\.[Ww][Tt][Vv]', args[0]):
            print 'Error: file is not a WTV recording.'
            exit(1)
    else:
        parser.print_help()
        exit(1)

class Subtitles:
    '''Extracts closed captions from source media using ccextractor and
    embeds them as SRT subtitles using MP4Box.'''
    subs = 1
    
    def __init__(self, source):
        self.source = source
        self.srt = source.base + '.srt'
        self.enabled = self.check()
        if not self.enabled:
            logging.warning('*** ccextractor not found, ' +
                            'subtitles disabled ***')
    
    def check(self):
        '''Determines whether ccextractor is present, and if so,
        stores the version number for later.'''
        ver = _ver(['ccextractor'], '(CCExtractor [0-9]+\.[0-9]+),')
        return ver is not None
    
    def extract(self, video):
        '''Obtains the closed-caption data embedded as VBI data within the
        filtered video clip and writes them to a SRT file.'''
        if not self.enabled:
            return
        logging.info('*** Extracting subtitles ***')
        _cmd(['ccextractor', '-o', self.srt, '-utf8', '-ve',
              '--no_progress_bar', video], expected = 232)
    
    def write(self):
        'Invokes MP4Box to embed the SRT subtitles into a MP4 file.'
        if not self.enabled:
            return
        arg = '%s:name=Subtitles:layout=0x125x0x-1' % self.srt
        _cmd(['MP4Box', '-tmp', self.source.opts.final_path, '-add',
              arg, self.source.mp4])
    
    def clean_tmp(self):
        'Removes temporary SRT files.'
        _clean(self.srt)

class Chapters:
    'Creates iOS-style chapter markers between designated cutpoints.'
    
    def __init__(self, source):
        self.source = source
        self._chap = source.base + '.xml'
        doc = xml.dom.minidom.Document()
        doc.appendChild(doc.createComment('GPAC 3GPP Text Stream'))
        stream = doc.createElement('TextStream')
        stream.setAttribute('version', '1.1')
        doc.appendChild(stream)
        header = doc.createElement('TextStreamHeader')
        stream.appendChild(header)
        sample = doc.createElement('TextSampleDescription')
        header.appendChild(sample)
        sample.appendChild(doc.createElement('FontTable'))
        self._doc = doc
    
    def add(self, pos, seg):
        '''Adds a new chapter marker at pos (in seconds).
        If seg is provided, the marker will be labelled 'Scene seg+1'.'''
        sample = self._doc.createElement('TextSample')
        sample.setAttribute('sampleTime', _seconds_to_time_frac(round(pos)))
        if seg is None:
            sample.setAttribute('text', '')
        else:
            text = self._doc.createTextNode('Scene %d' % (seg + 1))
            sample.appendChild(text)
            sample.setAttribute('xml:space', 'preserve')
        self._doc.documentElement.appendChild(sample)
    
    def write(self):
        '''Outputs the chapter data to XML format and invokes MP4Box to embed
        the chapter XML file into a MP4 file.'''
        _clean(self._chap)
        data = self._doc.toprettyxml(encoding = 'UTF-8', indent = '  ')
        logging.debug('Chapter XML file:')
        logging.debug(data)
        with open(self._chap, 'w') as dest:
            dest.write(data)
        args = ['MP4Box', '-tmp', self.source.opts.final_path,
                '-add', '%s:chap' % self._chap, self.source.mp4]
        try:
            _cmd(args)
        except RuntimeError:
            logging.warning('*** Old version of MP4Box, ' +
                            'chapter support unavailable ***')
    
    def clean_tmp(self):
        'Removes the temporary chapter XML file.'
        _clean(self._chap)

class Metadata:
    '''Translates previously fetched metadata (series name, episode name,
    episode number, credits...) into command-line arguments for AtomicParsley
    in order to embed it as iOS-compatible MP4 tags.'''
    _rating_ok = False
    _credits_ok = False
    
    def __init__(self, source):
        self.source = source
        self.enabled = self.check()
        if not self.enabled:
            logging.warning('*** AtomicParsley not found, ' +
                            'metadata disabled ***')
        elif not self._rating_ok or not self._credits_ok:
            logging.warning('*** Old version of AtomicParsley, ' +
                            'some functions unavailable ***')
    
    def check(self):
        '''Determines whether AtomicParsley is present, and if so, checks
        whether code to handle 'reverse DNS' style atoms (needed for content
        ratings and embedded XML credits) is present.'''
        ver = _ver(['AtomicParsley', '--help'], '(AtomicParsley)')
        if ver:
            rdns = ['AtomicParsley', '--reverseDNS-help']
            if _ver(rdns, '.*(--contentRating)'):
                self._rating_ok = True
            if _ver(rdns, '.*(--rDNSatom)'):
                self._credits_ok = True
            return True
        else:
            return False
    
    def _sort_credits(self):
        '''Browses through the previously obtained list of credited people
        involved with the episode and returns three separate lists of
        actors/hosts/guest stars, directors, and producers/writers.'''
        cast = []
        directors = []
        producers = []
        c = self.source.get('credits')
        for person in c:
            if person[1] in ['actor', 'host']:
                cast.append(person[0])
            elif person[1] == 'director':
                directors.append(person[0])
            elif person[1] == 'executive_producer':
                producers.append(person[0])
        for person in c:
            if person[1] == 'guest_star':
                cast.append(person[0])
            elif person[1] == 'producer':
                producers.append(person[0])
        for person in c:
            if person[1] == 'writer':
                producers.append(person[0])
        return cast, directors, producers
    
    def _make_section(self, people, key_name, xml, doc):
        '''Creates an XML branch named key_name, adds each person contained
        in people to an array within it, and appends the branch to xml, using
        the XML document doc.'''
        if len(people) > 0:
            key = doc.createElement('key')
            key.appendChild(doc.createTextNode(key_name))
            xml.appendChild(key)
            array = doc.createElement('array')
            xml.appendChild(array)
            for person in people:
                dic = doc.createElement('dict')
                key = doc.createElement('key')
                key.appendChild(doc.createTextNode('name'))
                dic.appendChild(key)
                name = doc.createElement('string')
                name.appendChild(doc.createTextNode(person))
                dic.appendChild(name)
                array.appendChild(dic)
    
    def _make_credits(self):
        '''Returns an iOS-compatible XML document listing the actors, directors
        and producers involved with the episode.'''
        (cast, directors, producers) = self._sort_credits()
        imp = xml.dom.minidom.getDOMImplementation()
        dtd = '-//Apple Computer//DTD PLIST 1.0//EN'
        url = 'http://www.apple.com/DTDs/PropertyList-1.0.dtd'
        dt = imp.createDocumentType('plist', dtd, url)
        doc = imp.createDocument(url, 'plist', dt)
        root = doc.documentElement
        root.setAttribute('version', '1.0')
        top = doc.createElement('dict')
        root.appendChild(top)
        self._make_section(cast, 'cast', top, doc)
        self._make_section(directors, 'directors', top, doc)
        self._make_section(producers, 'producers', top, doc)
        return doc
    
    def _perform(self, args):
        '''Invokes AtomicParsley with the provided command-line arguments. If
        the program is successful and outputs a new MP4 file with the newly
        embedded metadata, copies the new file over the old.'''
        self.clean_tmp()
        args = ['AtomicParsley', self.source.mp4] + args
        _cmd(args)
        for old in glob.glob(self.source.final + '-temp-*.' +
                             self.source.mp4ext):
            shutil.move(old, self.source.mp4)
    
    def _simple_tags(self, version):
        'Adds single-argument or standalone tags into the MP4 file.'
        s = self.source
        utc = s.time.strftime('%Y-%m-%dT%H:%M:%SZ')
        args = ['--stik', 'TV Show', '--encodingTool', version,
                '--purchaseDate', utc, '--grouping', 'MythTV Recording']
        if s.get('title') is not None:
            t = s['title']
            args += ['--artist', t, '--album', t, '--albumArtist', t,
                     '--TVShowName', t]
        if s.get('subtitle') is not None:
            args += ['--title', s['subtitle']]
        if s.get('category') is not None:
            args += ['--genre', s['category']]
        if s.get('originalairdate') is not None:
            args += ['--year', str(s['originalairdate'])]
        if s.get('channel') is not None:
            args += ['--TVNetwork', s['channel']]
        if s.get('syndicatedepisodenumber') is not None:
            args += ['--TVEpisode', s['syndicatedepisodenumber']]
        if s.get('episode') is not None and \
                s.get('episodecount') is not None:
            track = '%s/%s' % (s['episode'], s['episodecount'])
            args += ['--tracknum', track, '--TVEpisodeNum', s['episode']]
        if s.get('season') is not None and \
                s.get('seasoncount') is not None:
            disk = '%s/%s' % (s['season'], s['seasoncount'])
            args += ['--disk', disk, '--TVSeasonNum', s['season']]
        if s.get('rating') is not None and self._rating_ok:
            args += ['--contentRating', s['rating']]
        self._perform(args)
    
    def _longer_tags(self):
        '''Adds lengthier tags (such as episode description or series artwork)
        into the MP4 file separately, to avoid problems.'''
        s = self.source
        args = []
        if s.get('description') is not None:
            args += ['--description', s['description']]
        self._perform(args)
        if s.get('albumart') is not None:
            try:
                self._perform(['--artwork', s['albumart']])
            except RuntimeError:
                logging.warning('*** Could not embed artwork ***')
    
    def _credits(self):
        'Adds the credits XML data directly as a command-line argument.'
        c = self.source.get('credits')
        if c is not None and c != [] and self._credits_ok:
            doc = self._make_credits()
            args = ['--rDNSatom', doc.toxml(encoding = 'UTF-8'),
                    'name=iTunMOVI', 'domain=com.apple.iTunes']
            self._perform(args)
    
    def write(self, version):
        '''Performs each of the above steps involved in embedding metadata,
        using version as the encodingTool tag.'''
        if self.enabled:
            logging.info('*** Adding metadata to %s ***' % self.source.mp4)
            self._simple_tags(version)
            self._longer_tags()
            self._credits()
    
    def clean_tmp(self):
        'Removes any leftover MP4 files created by AtomicParsley.'
        files = u'%s-temp-*.%s' % (self.source.final, self.source.mp4ext)
        for old in glob.glob(files):
            _clean(old)

class Transcoder:
    '''Invokes tools necessary to extract, split, demux, encode, remux and
    finalize the media into MPEG-4 format.'''
    seg = 0
    _demux_v = None
    _demux_a = None
    _frames = 0
    _extra = 0
    _split_args = None
    
    def __init__(self, source, opts):
        self.source = source
        self.opts = opts
        self._demux = source.base + '-demux'
        self._wav = source.base + '.wav'
        self._h264 = source.base + '.h264'
        self._aac = source.base + '.aac'
        self._xcl = source.base + '.Xcl'
        self._xcl_data = StringIO.StringIO()
        self._xcl_data.write('CollectionPanel.CutMode=0\n')
        self.subtitles = Subtitles(source)
        self.chapters = Chapters(source)
        self.metadata = Metadata(source)
        self.check()
    
    def _nero_ver(self):
        '''Determines whether neroAacEnc is present, and if so, returns the
        version string for later.'''
        regex = 'Package version:\s*([0-9.]+)'
        ver = _ver(['neroAacEnc', '-help'], regex)
        if not ver:
            regex = 'Package build date:\s*([A-Za-z]+\s+[0-9]+\s+[0-9]+)'
            ver = _ver(['neroAacEnc', '-help'], regex)
        if ver:
            ver = 'Nero AAC Encoder %s' % ver
        return ver
    
    def _ffmpeg_ver(self):
        '''Determines whether ffmpeg is present, and if so, returns the
        version string for later.'''
        return _ver(['ffmpeg', '-version'], '([Ff]+mpeg.*)$',
                         use_stderr = False)
    
    def _x264_ver(self):
        '''Determines whether x264 is present, and if so, returns the
        version string for later. Does not check whether ffmpeg has libx264
        support linked in.'''
        return _ver(['x264', '--version'], '(x264.*)$')
    
    def _faac_ver(self):
        '''Determines whether ffmpeg is present, and if so, returns the
        version string for later. Does not check whether ffmpeg has libfaac
        support linked in.'''
        return _ver(['faac', '--help'], '(FAAC.*)$')
    
    def _projectx_ver(self):
        '''Determines whether Project-X is present, and if so, returns the
        version string for later.'''
        return _ver(['java', '-jar', self.opts.projectx, '-?'], \
                        '(ProjectX [0-9/.]*)')
    
    def version(self):
        'Compiles a string representing the versions of the encoding tools.'
        nero_ver = self._nero_ver()
        faac_ver = self._faac_ver()
        x264_ver = self._x264_ver()
        ver = self._ffmpeg_ver()
        if x264_ver:
            ver += ', %s' % x264_ver
        ver += ', %s' % self._projectx_ver()
        if self.opts.nero and nero_ver:
            ver += ', %s' % nero_ver
        elif faac_ver:
            ver += ', %s' % faac_ver
        logging.debug('Version string: %s' % ver)
        return ver
    
    def check(self):
        '''Determines whether ffmpeg is installed and has built-in support
        for the requested encoding method.'''
        codecs = ['ffmpeg', '-codecs']
        if not self._ffmpeg_ver():
            raise RuntimeError('FFmpeg is not installed.')
        if not _ver(codecs, '--enable-(libx264)'):
            raise RuntimeError('FFmpeg does not support libx264.')
        if not self.opts.nero and not _ver(codecs, '--enable-(libfaac)'):
            raise RuntimeError('FFmpeg does not support libfaac. ' +
                               '(Perhaps try using neroAacEnc?)')
        if self.opts.nero and not self._nero_ver():
            raise RuntimeError('neroAacEnc is not installed.')
        if not _ver(['MP4Box', '-version'], 'version\s*([0-9.DEV]+)'):
            raise RuntimeError('MP4Box is not installed.')
        if not self.source.meta_present:
            self.metadata.enabled = False
    
    def _check_split_args(self):
        '''Determines the arguments to pass to FFmpeg when performing queries
        on bytecode positions. Versions 0.7 and older use -newaudio /
        -newvideo tags for each additional stream present. Versions 0.8 and
        newer use -map 0:v -map 0:a to automatically copy over all streams.'''
        match = re.search('[Ff]+mpeg\s+(.*)$', self._ffmpeg_ver())
        if not match:
            raise RuntimeError('FFmpeg version could not be determined.')
        ver = match.group(1)
        match = re.match('^([0-9]+\.[0-9]+)', ver)
        if match and float(match.group(1)) <= 0.7:
            args = ['-acodec', 'copy', '-vcodec', 'copy',
                    '-f', 'mpeg', 'pipe:']
            for astream in xrange(1, len(self.source.astreams)):
                args += ['-acodec', 'copy', '-newaudio']
            for vstream in xrange(1, len(self.source.vstreams)):
                args += ['-vcodec', 'copy', '-newvideo']
        else:
            args = ['-map', '0:v', '-map', '0:a', '-c', 'copy',
                    '-f', 'mpeg', 'pipe:']
        return args
    
    def _count_frames(self, pipe):
        '''Obtains the frame count for a video file from the ffmpeg stderr
        pipe within a separate thread while video data is read from stdout
        by the main thread.'''
        frames = 0
        regex = re.compile('frame=([0-9]+)(?!.*frame)')
        for line in pipe:
            if self.opts.verbose:
                logging.debug(line.replace('\n', ''))
            match = re.search(regex, line)
            if match:
                frames = int(match.group(1))
        self._frames = frames
    
    def _compensate(self, block = 1024 * 4096):
        '''Some video files include extra VBI data which can throw off
        cutpoint calculations, resulting in inaccurate commercial cuts.
        To compensate for this, the video is remuxed using ffmpeg while
        preserving as much data as possible, and the data is counted
        block bytes at a time while the frame count is obtained through
        the status output in another thread.'''
        bc = 0
        args = ['ffmpeg', '-y', '-i', self.source.orig] + self._split_args
        logging.info('*** Indexing video ***')
        logging.debug('$ %s' % u' '.join(args))
        proc = subprocess.Popen(args, stdout = subprocess.PIPE,
                                stderr = subprocess.PIPE)
        thr = threading.Thread(target = self._count_frames,
                               args = ([proc.stderr]))
        thr.start()
        data = proc.stdout.read(block)
        bc += len(data)
        while data:
            data = proc.stdout.read(block)
            bc += len(data)
        self._extra = os.stat(self.source.orig).st_size - bc
        thr.join()
        proc.wait()
        if proc.returncode != 0:
            raise RuntimeError('Unexpected return code', u' '.join(args),
                               proc.returncode)
        logging.debug('Frames: %d, extra bytes: %d' %
                      (self._frames, self._extra))
    
    def _frame_to_bytecode(self, frame, block = 1024 * 4096):
        '''Obtains the byte offset into a video file of a particular frame
        number by invoking ffmpeg to remux the entire file to that point
        and checking the resulting filesize by reading the data block bytes
        at a time, compensating for any potential lost data.'''
        bc = 0
        with open(os.devnull, 'w') as devnull:
            args = ['ffmpeg', '-y', '-i', self.source.orig, '-vframes',
                    str(frame)] + self._split_args
            logging.debug('$ %s' % u' '.join(args))
            proc = subprocess.Popen(args, stdout = subprocess.PIPE,
                                    stderr = devnull)
            data = proc.stdout.read(block)
            bc = len(data)
            while data:
                data = proc.stdout.read(block)
                bc += len(data)
            proc.wait()
            if proc.returncode != 0:
                raise RuntimeError('Unexpected return code', u' '.join(args),
                                   proc.returncode)
        if self._extra > 0 and self._frames > 0:
            bc = int(round(bc + self._extra * 1. / self._frames * frame))
        return bc
    
    def _extract(self, clip, elapsed):
        '''Creates a new chapter marker at elapsed and adds an entry in the
        Project-X cutlist for clip. All values are in seconds.'''
        logging.info('*** Locating segment %d: [%s - %s] ***' %
                     (self.seg, _seconds_to_time(clip[0]),
                      _seconds_to_time(clip[1])))
        self.chapters.add(elapsed, self.seg)
        frame = (int(round(clip[0] * self.source.fps)),
                 int(round(clip[1] * self.source.fps)))
        self._xcl_data.write('%d\n' % self._frame_to_bytecode(frame[0]))
        self._xcl_data.write('%d\n' % self._frame_to_bytecode(frame[1]))
        self.seg += 1
    
    def _find_split(self):
        'Uses the Project-X log to obtain the clipped / filtered video file.'
        with open('%s_log.txt' % self.source.base, 'r') as log:
            regex = re.compile('.*new File:\s+(.*)\s*$')
            for line in log:
                match = re.search(regex, line)
                if match:
                    self._split = match.group(1)
    
    def split(self):
        '''Uses the source's cutlist to mark specific video clips from the
        source video for extraction while also setting chapter markers and
        obtaining subtitles, and then invokes Project-X to split and join
        the source video.'''
        pos = 0
        elapsed = 0
        self.subtitles.clean_tmp()
        self._split_args = self._check_split_args()
        self._compensate()
        for cut in self.source.cutlist:
            (start, end) = cut
            if start > self.opts.thresh and start > pos:
                self._extract((pos, start), elapsed)
            elapsed += start - pos
            pos = end
        if pos < self.source.duration - self.opts.thresh:
            self._extract((pos, self.source.duration), elapsed)
            elapsed += self.source.duration - pos
            pos = self.source.duration
        self.chapters.add(elapsed, None)
        logging.debug('Xcl cutlist:')
        logging.debug(self._xcl_data.getvalue())
        with open(self._xcl, 'w') as xcl:
            xcl.write(self._xcl_data.getvalue())
        name = os.path.split(self.source.base)[-1]
        if len(self.source.cutlist) > 0:
            logging.info('*** Clipping commercials from video ***')
        try:
            _cmd(['java', '-jar', self.opts.projectx, '-out', self.opts.tmp,
                  '-name', name, '-cut', self._xcl, '-filter',
                  self.source.orig])
        except RuntimeError:
            raise RuntimeError('Could not split video.')
        self._find_split()
        if not os.path.exists(self._split):
            raise RuntimeError('Could not locate split video.')
        self.subtitles.extract(self._split)
    
    def _find_demux(self):
        'Uses the Project-X log to obtain the separated video / audio files.'
        with open('%s_log.txt' % self._demux, 'r') as log:
            videoRE = re.compile('Video: PID 0x([0-9A-Fa-f]+)')
            audioRE = re.compile('Audio: PID 0x([0-9A-Fa-f]+)')
            fileRE = re.compile('\'(.*)\'\s*$')
            (curr_v, curr_a) = (1, 1)
            (found_v, found_a) = (0, 0)
            (targ_v, targ_a) = (0, 0)
            for line in log:
                match = re.search(videoRE, line)
                if match:
                    found_v += 1
                    pid = int(match.group(1), 16)
                    for vid in self.source.vstreams:
                        if vid[0] == pid and vid[1]:
                            targ_v = found_v
                match = re.search(audioRE, line)
                if match:
                    found_a += 1
                    pid = int(match.group(1), 16)
                    for aud in self.source.astreams:
                        if aud[0] == pid and aud[1]:
                            targ_a = found_a
                if re.match('\.Video ', line):
                    if curr_v == targ_v:
                        match = re.search(fileRE, line)
                        if match:
                            self._demux_v = match.group(1)
                    curr_v += 1
                elif re.match('Audio \d', line):
                    if curr_a == targ_a:
                        match = re.search(fileRE, line)
                        if match:
                            self._demux_a = match.group(1)
                    curr_a += 1
    
    def demux(self):
        '''Invokes Project-X to clean noise from raw MPEG-2 video capture data,
        split the media along previously specified cutpoints and combine into
        one file, and then extract each media stream (video / audio) from the
        container into separate raw data files.'''
        logging.info('*** Demuxing video ***')
        name = os.path.split(self._demux)[-1]
        try:
            _cmd(['java', '-jar', self.opts.projectx, '-out', self.opts.tmp,
                  '-name', name, '-cut', self._xcl, '-demux',
                  self.source.orig])
        except RuntimeError:
            raise RuntimeError('Could not demux video.')
        self._find_demux()
        if self._demux_v is None or not os.path.exists(self._demux_v):
            raise RuntimeError('Could not locate demuxed video stream.')
        if self._demux_a is None or not os.path.exists(self._demux_a):
            raise RuntimeError('Could not locate demuxed audio stream.')
        logging.debug('Demuxed video: %s' % self._demux_v)
        logging.debug('Demuxed audio: %s' % self._demux_a)
    
    def _adjust_res(self):
        '''If the iPod-compatible flag is selected, adjusts the target
        resolution to be exactly 640x480, preserving aspect ratio by padding
        extra space with black pixels.'''
        size = []
        res = self.source.resolution
        if self.opts.ipod:
            aspect = res[0] * 1.0 / res[1]
            if aspect > 640.0 / 480.0:
                vres = int(round(640.0 / aspect))
                if vres % 2 == 1:
                    vres += 1
                pad = (480 - vres) / 2
                size = ['-s', '640x%d' % vres, '-vf',
                        'pad=640:480:0:%d:black' % pad]
            else:
                hres = int(round(480.0 / aspect))
                if hres % 2 == 1:
                    hres += 1
                pad = (640 - hres) / 2
                size = ['-s', '%dx480' % hres, '-vf',
                        'pad=640:480:%d:0:black' % pad]
        return size
    
    def encode_video(self):
        'Invokes ffmpeg to transcode the video stream to H.264.'
        _clean(self._h264)
        prof = []
        fmt = 'mp4'
        if self.opts.preset:
            prof = ['-vpre', self.opts.preset]
        if self.opts.ipod:
            fmt = 'ipod'
            if self.opts.ipod_preset:
                prof = ['-vpre', self.opts.ipod_preset]
        size = self._adjust_res()
        common = ['ffmpeg', '-y', '-i', self._demux_v, '-vcodec', 'libx264',
                  '-an', '-threads', 0, '-f', fmt] + prof + size
        if self.opts.two_pass:
            logging.info(u'*** Encoding video to %s - first pass ***' %
                         self.opts.tmp)
            common += ['-vb', '%dk' % self.opts.video_br]
            _cmd(common + ['-pass', 1, os.devnull],
                 cwd = self.opts.tmp)
            logging.info(u'*** Encoding video to %s - second pass ***' %
                         self._h264)
            _cmd(common + ['-pass', 2, self._h264],
                 cwd = self.opts.tmp)
        else:
            logging.info(u'*** Encoding video to %s ***' % self._h264)
            _cmd(common + ['-crf', self.opts.video_crf, self._h264])
    
    def encode_audio(self):
        'Invokes ffmpeg or neroAacEnc to transcode the audio stream to AAC.'
        logging.info(u'*** Encoding audio to %s ***' % self._aac)
        if self.opts.nero:
            _cmd(['ffmpeg', '-y', '-i', self._demux_a, '-vn', '-acodec',
                  'pcm_s16le', '-f', 'wav', self._wav])
            _clean(self._aac)
            _cmd(['neroAacEnc', '-q', self.opts.audio_q, '-if', self._wav,
                  '-of', self._aac])
        else:
            _cmd(['ffmpeg', '-y', '-i', self._demux_a, '-vn', '-acodec',
                  'libfaac', '-ab', '%dk' % self.opts.audio_br, '-f', 'aac',
                  self._aac])
    
    def remux(self):
        '''Invokes MP4Box to combine the audio, video and subtitle streams
        into the MPEG-4 target file, also embedding chapter data and
        metadata.'''
        logging.info(u'*** Remuxing to %s ***' % self.source.mp4)
        self.source.make_final_dir()
        _clean(self.source.mp4)
        common = ['MP4Box', '-tmp', self.opts.final_path]
        _cmd(common + ['-new', '-add', '%s#video:name=Video' % self._h264,
                       '-add', '%s#audio:name=Audio' % self._aac,
                       self.source.mp4])
        _cmd(common + ['-isma', '-hint', self.source.mp4])
        self.subtitles.write()
        self.chapters.write()
        _cmd(common + ['-lang', self.opts.language, self.source.mp4])
        self.metadata.write(self.version())
    
    def clean_video(self):
        'Removes the temporary video stream data.'
        _clean(self._demux_v)
    
    def clean_audio(self):
        'Removes the temporary audio stream data.'
        _clean(self._demux_a)
    
    def clean_tmp(self):
        'Removes any temporary files generated during encoding.'
        self.clean_video()
        self.clean_audio()
        _clean(self._split)
        _clean(self._wav)
        _clean(self._aac)
        _clean(self._h264)
        _clean(self._xcl)
        for log in ['ffmpeg2pass-0.log', 'x264_2pass.log',
                    'x264_2pass.log.mbtree', '%s_log.txt' % self._demux,
                    '%s_log.txt' % self.source.base]:
            _clean(os.path.join(self.opts.tmp, log))
        self.subtitles.clean_tmp()
        self.chapters.clean_tmp()
        self.metadata.clean_tmp()

class Source(dict):
    '''Acts as a base class for various raw video sources and handles
    Tvdb metadata.'''
    fps = None
    resolution = None
    duration = None
    cutlist = None
    vstreams = []
    astreams = []
    base = None
    orig = None
    rating = None
    final = None
    mp4 = None
    meta_present = False
    
    def __repr__(self):
        season = int(self.get('season', 0))
        episode = int(self.get('episode', 0))
        prodcode = self.get('syndicatedepisodenumber', '(?)')
        show = self.get('title')
        name = self.get('subtitle')
        s = ''
        if show and name:
            if season > 0 and episode > 0:
                s = u'%s %02dx%02d - %s' % (show, season, episode, name)
            else:
                s = u'%s %s - %s' % (show, prodcode, name)
        else:
            s = self.base
        return u'<Source \'%s\' at %s>' % (s, hex(id(self)))
    
    def __init__(self, opts):
        self.opts = opts
        if opts.tmp:
            self.remove_tmp = False
        else:
            opts.tmp = tempfile.mkdtemp(prefix = u'transcode_')
            self.remove_tmp = True
        if opts.ipod:
            self.mp4ext = 'm4v'
        else:
            self.mp4ext = 'mp4'
        self.tvdb = MythTV.ttvdb.tvdb_api.Tvdb(language = self.opts.language)
    
    def video_params(self):
        '''Obtains source media parameters such as resolution and FPS
        using ffmpeg.'''
        (fps, resolution, duration) = (None, None, None)
        (vstreams, astreams) = ([], [])
        stream = 'Stream.*\[0x([0-9a-fA-F]+)\].*'
        fpsRE = re.compile('([0-9]*\.?[0-9]*) tbr')
        videoRE = re.compile(stream + 'Video:.*\s+([0-9]+)x([0-9]+)')
        audioRE = re.compile(stream + ':\s*Audio')
        duraRE = re.compile('Duration: ([0-9]+):([0-9]+):([0-9]+)\.([0-9]+)')
        try:
            proc = subprocess.Popen(['ffmpeg', '-i', self.orig],
                                    stdout = subprocess.PIPE,
                                    stderr = subprocess.STDOUT)
            for line in proc.stdout:
                match = re.search(fpsRE, line)
                if match:
                    fps = float(match.group(1))
                match = re.search(videoRE, line)
                if match:
                    enabled = False
                    if re.search('Video:.*\(Main\)', line):
                        logging.debug('Found video stream 0x%s' %
                                      match.group(1))
                        enabled = True
                    vstreams += [(int(match.group(1), 16), enabled)]
                    if resolution is None:
                        width = int(match.group(2))
                        height = int(match.group(3))
                        resolution = (width, height)
                match = re.search(audioRE, line)
                if match:
                    enabled = False
                    pid = int(match.group(1), 16)
                    match = re.search('\]\(([A-Za-z]+)\)', line)
                    if match:
                        if match.group(1) == _iso_639_2(self.opts.language):
                            logging.debug('Found audio stream 0x%s' %
                                          match.group(1))
                            enabled = True
                    astreams += [(pid, enabled)]
                match = re.search(duraRE, line)
                if match:
                    hour = int(match.group(1))
                    minute = int(match.group(2))
                    sec = int(match.group(3))
                    frac = int(match.group(4))
                    duration = hour * 3600 + minute * 60 + sec + \
                        frac / (10. ** len(match.group(4)))
            proc.wait()
        except OSError:
            raise RuntimeError('FFmpeg is not installed.')
        if len(vstreams) == 0:
            raise RuntimeError('No video streams could be found.')
        if len(astreams) == 0:
            raise RuntimeError('No audio streams could be found.')
        if len([vid[0] for vid in vstreams if vid[1]]) == 0:
            logging.debug('No detected video streams, enabling %s' %
                          hex(vstreams[0][0]))
            vstreams[0] = (vstreams[0][0], True)
        if len([aud[0] for aud in astreams if aud[1]]) == 0:
            logging.debug('No detected audio streams, enabling %s' %
                          hex(astreams[0][0]))
            astreams[0] = (astreams[0][0], True)
        return fps, resolution, duration, vstreams, astreams
    
    def _align_episode(self):
        '''Returns a string for the episode number padded by as many zeroes
        needed so that the filename for the last episode in the season will
        align perfectly with this filename. Usually a field width of two,
        since most seasons tend to have less than 100 episodes.'''
        ep = self.get('episode')
        if ep is None:
            ep = ''
        if self.get('episodecount') is None:
            return ep
        field = int(math.ceil(math.log(self['episodecount']) /
                              math.log(10)))
        return ('%0' + str(field) + 'd') % ep
    
    def _find_episode(self, show):
        'Searches Tvdb for the episode using the original air date and title.'
        episodes = None
        airdate = self.get('originalairdate')
        subtitle = self.get('subtitle')
        if airdate is not None:
            episodes = show.search(airdate, key = 'firstaired')
        if not episodes and subtitle is not None:
            episodes = show.search(subtitle, key = 'episodename')
        if len(episodes) == 1:
            return episodes[0]
        for ep in episodes:
            air = ep.get('firstaired')
            if air:
                date = datetime.datetime.strptime(air, '%Y-%m-%d').date()
                if airdate == date:
                    return ep
        for ep in episodes:
            st = ep.get('episodename')
            if subtitle.find(st) >= 0 or st.find(subtitle) >= 0:
                return ep
        return None
    
    def fetch_tvdb(self):
        'Obtains missing metadata through Tvdb if episode is found.'
        if not self.get('title'):
            return
        try:
            show = self.tvdb[self.get('title')]
            self['seasoncount'] = len(show)
            if show.has_key(0):
                self['seasoncount'] -= 1
            ep = self._find_episode(show)
            logging.debug('Tvdb episode: %s' % ep)
            if ep:
                if self.get('subtitle') is None:
                    self['subtitle'] = ep.get('episodename')
                if ep.get('episodenumber') is not None:
                    self['episode'] = int(ep.get('episodenumber'))
                elif ep.get('combined_episodenumber') is not None:
                    self['episode'] = int(ep.get('combined_episodenumber'))
                season = ep.get('seasonnumber')
                if season is None:
                    season = int(ep.get('combined_season'))
                if season is not None:
                    self['episodecount'] = len(show[int(season)])
                    self['season'] = int(season)
                if self['season'] is not None and self['episode'] is not None:
                    if self.get('syndicatedepisodenumber') is None:
                        self['syndicatedepisodenumber'] = '%d%s' % \
                            (self['season'], self._align_episode())
                overview = ep.get('overview')
                if self.get('description') is None:
                    self['description'] = overview
                elif overview is not None:
                    if self.opts.prefer_tvdb_descriptions:
                        if len(self['description']) < len(overview):
                            self['description'] = overview
                rating = ep.get('rating')
                if rating is not None:
                    self['popularity'] = int(float(rating) / 10 * 255)
                    if self.opts.use_tvdb_rating:
                        self['description'] += ' (%s / 10)' % rating
                filename = ep.get('filename')
                if filename is not None and len(filename) > 0:
                    ext = os.path.splitext(filename)[-1]
                    art = self.base + ext
                    try:
                        urllib.urlretrieve(filename, art)
                        self['albumart'] = art
                    except IOError:
                        logging.warning('*** Unable to download ' +
                                        'episode screenshot ***')
        except MythTV.ttvdb.tvdb_exceptions.tvdb_shownotfound:
            logging.warning('*** Unable to fetch Tvdb listings for show ***')
    
    def sort_credits(self):
        '''Sorts the list of credited actors, directors and such using the
        last name first.'''
        if self.get('credits'):
            key = lambda person: u'%s %s' % (person[1],
                                             _last_name_first(person[0]))
            self['credits'] = sorted(self.get('credits'), key = key)
    
    def print_metadata(self):
        'Outputs any metadata obtained to the log.'
        if not self.meta_present:
            return
        logging.info('*** Printing file metadata ***')
        for key in self.keys():
            if key != 'credits':
                logging.info(u'  %s: %s' % (key, self[key]))
        cred = self.get('credits')
        if cred:
            logging.info('  Credits:')
            for person in cred:
                name = person[0]
                role = re.sub('_', ' ', person[1]).lower()
                logging.info(u'    %s (%s)' % (name, role))
        else:
            logging.info('  No credits')
    
    def final_name(self):
        '''Obtains the filename of the target MPEG-4 file using the format
        string. Formatting is (mostly) compatible with Recorded.formatPath()
        from dataheap.py, and the format used in mythrename.pl.'''
        final = os.path.join(self.opts.final_path,
                             os.path.split(self.base)[-1])
        if self.meta_present:
            path = self.opts.final_format
            tags = [('%T', 'title'), ('%S', 'subtitle'), ('%R', 'description'),
                    ('%C', 'category'), ('%n', 'syndicatedepisodenumber'),
                    ('%s', 'season'), ('%E', 'episode'), ('%r', 'rating')]
            for tag, key in tags:
                if self.get(key) is not None:
                    val = unicode(self.get(key))
                    val = val.replace('/', self.opts.replace_char)
                    if os.name == 'nt':
                        val = val.replace('\\', self.opts.replace_char)
                    path = path.replace(tag, val)
                else:
                    path = path.replace(tag, '')
            if self.get('episode') is not None:
                path = path.replace('%e', self._align_episode())
            else:
                path = path.replace('%e', '')
            tags = [('%oy', '%y'), ('%oY', '%Y'), ('%on', '%m'),
                    ('%om', '%m'), ('%oj', '%d'), ('%od', '%d')]
            airdate = self.get('originalairdate')
            for tag, part in tags:
                if airdate is not None:
                    val = unicode(airdate.strftime(part))
                    path = path.replace(tag, val)
                else:
                    path = path.replace(tag, '')
            path = path.replace('%-', '-')
            path = path.replace('%%', '%')
            path = _sanitize(path, self.opts.replace_char)
            final = os.path.join(self.opts.final_path, *path.split('/'))
        logging.debug('Final name: %s' % final)
        return final
    
    def make_final_dir(self):
        'Creates the directory for the target MPEG-4 file.'
        path = os.path.dirname(self.final)
        if not os.path.isdir(path):
            os.makedirs(path, 0755)
    
    def clean_copy(self):
        'Removes the copied raw MPEG-2 video data.'
        _clean(self.orig)
    
    def clean_tmp(self):
        'Removes any temporary files created.'
        self.clean_copy()
        art = self.get('albumart')
        if art:
            _clean(art)
        if self.remove_tmp and os.path.isdir(self.opts.tmp):
            shutil.rmtree(self.opts.tmp)

class MythSource(Source):
    '''Obtains the raw MPEG-2 video data from a MythTV database along with
    metadata and a commercial-skip cutlist.'''
    prog = None
    
    class _Rating(MythTV.DBDataRef):
        'Query for the content rating within the MythTV database.'
        _table = 'recordedrating'
        _ref = ['chanid', 'starttime']
    
    def __init__(self, channel, time, opts):
        Source.__init__(self, opts)
        self.channel = channel
        self.time = _convert_time(time)
        self.base = os.path.join(opts.tmp, '%s_%s' % (str(channel), str(time)))
        self.orig = self.base + '-orig.mpg'
        self.db = MythTV.MythDB(DBHostName = opts.host,
                                DBName = opts.database,
                                DBUserName = opts.user,
                                DBPassword = opts.password,
                                SecurityPin = opts.pin)
        try:
            self.rec = MythTV.Recorded((channel, time), db = self.db)
        except MythTV.exceptions.MythError:
            err = 'Could not find recording at channel %d and time %s.'
            raise ValueError(err % (channel, time))
        try:
            self.prog = self.rec.getRecordedProgram()
            self.meta_present = True
        except MythTV.exceptions.MythError:
            logging.warning('*** No MythTV program data, ' +
                            'metadata disabled ***')
        self.rating = self._Rating(self.rec._wheredat, self.db)
        self._fetch_metadata()
        self.final = self.final_name()
        self.mp4 = '%s.%s' % (self.final, self.mp4ext)
    
    def _cut_list(self):
        'Obtains the MythTV commercial-skip cutlist from the database.'
        cl = self.rec.markup.getcutlist()
        self.cutlist = []
        for i in xrange(0, len(cl)):
            self.cutlist.append((cl[i][0] / self.fps, cl[i][1] / self.fps))
    
    def _fetch_metadata(self):
        'Obtains any metadata MythTV might have stored in the database.'
        if not self.meta_present:
            return
        logging.info('*** Fetching metadata for %s ***' % self.base)
        channel = None
        ch = MythTV.Channel(db = self.db)
        for chan in ch._fromQuery("", (), db = self.db):
            if chan.get('chanid') == self.rec.get('chanid'):
                channel = chan
        if channel:
            self['channel'] = channel.get('name')
        for key in ['title', 'subtitle', 'description', 'category',
                    'originalairdate', 'syndicatedepisodenumber']:
            val = self.prog.get(key)
            if val is not None:
                self[key] = val
        if self.rec.get('originalairdate') is None: # MythTV bug
            self.rec['originalairdate'] = self.time
        for item in self.rating:
            self['rating'] = item.get('rating')
        cred = None
        for person in self.rec.cast:
            if cred is None:
                cred = []
            cred.append((person['name'], person['role']))
        self['credits'] = cred
        self.sort_credits()
        self.fetch_tvdb()
    
    def copy(self):
        '''Copies the recording for the given channel ID and start time to the
        specified path, if enough space is available.'''
        bs = 4096 * 1024
        logging.info('*** Copying video to %s ***' % self.orig)
        source = self.rec.open()
        try:
            with open(self.orig, 'wb') as dest:
                data = source.read(bs);
                while len(data) > 0:
                    dest.write(data)
                    data = source.read(bs)
        finally:
            source.close()
        (self.fps, self.resolution, self.duration,
         self.vstreams, self.astreams) = self.video_params()
        if not self.fps or not self.resolution or not self.duration:
            raise RuntimeError('Could not determine video parameters.')
        self._cut_list()

class WTVSource(Source):
    '''Obtains the raw MPEG-2 video data from a Windows TV recording (.WTV)
    along with embedded metadata.'''
    channel = None
    time = None
    orig = None
    
    def __init__(self, wtv, opts):
        Source.__init__(self, opts)
        self.wtv = wtv
        match = re.search('[^_]*_([^_]*)_(\d\d\d\d)_(\d\d)_(\d\d)_' +
                          '(\d\d)_(\d\d)_(\d\d)\.[Ww][Tt][Vv]', wtv)
        if match:
            self.channel = match.group(1)
            t = ''
            for g in xrange(2, 8):
                t += match.group(g)
            self.time = _convert_time(long(t))
            b = self.channel + '_' + t
            self.base = os.path.join(opts.tmp, '%s_%s' % (self.channel, t))
        else:
            f = os.path.split(wtv)[1]
            self.base = os.path.join(opts.tmp, os.path.splitext(f)[0])
        self.orig = self.base + '-orig.ts'
        self._fetch_metadata()
        self.final = self.final_name()
        self.mp4 = '%s.%s' % (self.final, self.mp4ext)
    
    def _cut_list(self):
        '''Obtains a commercial-skip cutlist from previously generated
        Comskip output, if it exists.'''
        self.cutlist = []
        base = os.path.splitext(self.wtv)[0]
        comskip = base + '.txt'
        if os.path.exists(comskip):
            framesRE = re.compile('^(\d+)\s+(\d+)\s*$')
            with open(comskip, 'r') as text:
                for line in text:
                    match = re.search(framesRE, line)
                    if match:
                        start = int(match.group(1)) / self.fps
                        end = int(match.group(2)) / self.fps
                        self.cutlist.append((start, end))
    
    def _parse_genre(self, genre):
        'Translates the WTV genre line into a category tag.'
        self['category'] = genre.split(';')[0]
    
    def _parse_airdate(self, airdate):
        'Translates the UTC timecode for original airdate into a date object.'
        try:
            d = datetime.datetime.strptime(airdate, '%Y-%m-%dT%H:%M:%SZ')
            self['originalairdate'] = d.date()
        except ValueError:
            pass
    
    def _parse_credits(self, line):
        'Translates the WTV credits line into a list of credited people.'
        cred = None
        people = line.split(';')
        for tup in zip(range(0, 4), ['actor', 'director',
                                     'host', 'guest_star']):
            for person in people[tup[0]].split('/'):
                if person != '':
                    if cred is None:
                        cred = []
                    cred.append((person, tup[1]))
        self['credits'] = cred
    
    def _fetch_metadata(self):
        'Obtains any metadata which might be embedded in the WTV.'
        logging.info('*** Fetching metadata for %s ***' % self.wtv)
        val = '\s*:\s*(.*)$'
        tags = []
        tags.append((re.compile('service_provider' + val), 'channel'))
        tags.append((re.compile('service_name' + val), 'channel'))
        #tags.append((re.compile('WM/MediaNetworkAffiliation' + val),
        #             'channel'))
        tags.append((re.compile('\s+Title' + val), 'title'))
        tags.append((re.compile('WM/SubTitle' + val), 'subtitle'))
        tags.append((re.compile('WM/SubTitleDescription' + val),
                     'description'))
        tags.append((re.compile('genre' + val), self._parse_genre))
        tags.append((re.compile('WM/MediaOriginalBroadcastDateTime' + val),
                     self._parse_airdate))
        tags.append((re.compile('WM/ParentalRating' + val), 'rating'))
        tags.append((re.compile('WM/MediaCredits' + val), self._parse_credits))
        try:
            proc = subprocess.Popen(['ffmpeg', '-i', self.wtv],
                                    stdout = subprocess.PIPE,
                                    stderr = subprocess.STDOUT)
            for line in proc.stdout:
                for tag in tags:
                    match = re.search(tag[0], line)
                    if match:
                        self.meta_present = True
                        if type(tag[1]) == type(str()):
                            self[tag[1]] = match.group(1).strip()
                        else:
                            tag[1](match.group(1).strip())
            proc.wait()
        except OSError:
            raise RuntimeError('FFmpeg is not installed.')
        self.sort_credits()
        self.fetch_tvdb()
    
    def copy(self):
        'Extracts the MPEG-2 data from the WTV file.'
        logging.info('*** Extracting data to %s ***' % self.orig)
        try:
            _cmd(['java', '-cp', self.opts.remuxtool, 'util.WtvToMpeg',
                  '-i', self.wtv, '-o', self.orig, '-lang',
                  _iso_639_2(self.opts.language)])
        except RuntimeError:
            raise RuntimeError('Could not extract video.')
        self._fetch_metadata()
        (self.fps, self.resolution, self.duration,
         self.vstreams, self.astreams) = self.video_params()
        if not self.fps or not self.resolution or not self.duration:
            raise RuntimeError('Could not determine video parameters.')
        self._cut_list()

if __name__ == '__main__':
    sys.stdout = codecs.getwriter('utf8')(sys.stdout)
    parser = _get_options()
    (opts, args) = parser.parse_args()
    _check_args(args, parser)
    loglvl = logging.INFO
    if opts.verbose:
        loglvl = logging.DEBUG
    if opts.quiet:
        loglvl = logging.CRITICAL
    logging.basicConfig(format = '%(message)s', level = loglvl)
    s = None
    if len(args) == 1:
        wtv = args[0]
        s = WTVSource(wtv, opts)
    else:
        channel = int(args[0])
        timecode = long(args[1])
        s = MythSource(channel, timecode, opts)
    s.copy()
    s.print_metadata()
    t = Transcoder(s, opts)
    t.split()
    t.demux()
    s.clean_copy()
    t.encode_audio()
    t.clean_audio()
    t.encode_video()
    t.clean_video()
    t.remux()
    t.clean_tmp()
    s.clean_tmp()

# Copyright (c) 2012, Lucas Jacobs
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met: 
#
# 1. Redistributions of source code must retain the above copyright notice,
#    this list of conditions and the following disclaimer. 
# 2. Redistributions in binary form must reproduce the above copyright notice,
#    this list of conditions and the following disclaimer in the documentation
#    and/or other materials provided with the distribution. 
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
# LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
# CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
# SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
# INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
# CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
# ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
# POSSIBILITY OF SUCH DAMAGE.
#
# The views and conclusions contained in the software and documentation are
# those of the authors and should not be interpreted as representing official
# policies, either expressed or implied, of the copyright holder.
