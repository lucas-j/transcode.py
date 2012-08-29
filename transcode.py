#!/usr/bin/env python
# -*- coding: utf-8 -*-

'''
This program uses a MythTV database or WTV recording to transcode
recorded TV programs to MPEG-4 or Matroska video using the H.264/AAC
or VP8/Vorbis/FLAC codecs, cutting the video at certain commercial points
detected by either MythTV or by Comskip. The resulting video file comes
complete with SRT subtitles extracted from the embedded VBI closed-caption
data. and iTunes-compatible metadata about the episode, if it can be found.

In short, this program calls a bunch of programs to convert a file like
1041_20100523000000.mpg or Program Name_ABC_2010_05_23_00_00_00.wtv into a
file like ~/Videos/Program Name/Program Name - Episode Name.mp4,
including captions, file tags, chapters, and with commercials removed.

This program has been tested on Windows, Linux and FreeBSD, and can optionally
transcode from remote sources - e.g., mythbackend / MySQL running on a
different computer, or WTV source files from a remote SMB share / HomeGroup.

Requirements:
- FFmpeg (http://ffmpeg.org)
- Java (http://www.java.com)
- Project-X (http://project-x.sourceforge.net)
- remuxTool.jar (http://babgvant.com/downloads/dburckh/remuxTool.jar)
- Python 2.7 (http://www.python.org)
  - lxml (http://lxml.de)
  - mysql-python (http://sourceforge.net/projects/mysql-python)
  - the MythTV Python bindings (if MythTV is not installed already)

For MPEG-4 / H.264:
- MP4Box (http://gpac.sourceforge.net)
- neroAacEnc (http://www.nero.com/enu/technologies-aac-codec.html)
- FFmpeg must be compiled with --enable-libx264
- if using faac for audio, FFmpeg must be compiled with --enable-libfaac

For Matroska / VP8:
- MKVToolNix (http://www.bunkus.org/videotools/mkvtoolnix/)
- FFmpeg must be compiled with --enable-libvpx and --enable-libvorbis

Optional dependencies:
- ccextractor (http://ccextractor.sourceforge.net)
- AtomicParsley (https://bitbucket.org/wez/atomicparsley)

Most of these packages can usually be found in various Linux software
repositories or as pre-compiled Windows binaries.

Setup:
- Make sure the above dependencies are installed on your system. Add each
  binary location to your PATH variable if necessary.
- Edit the settings in transcode.conf to your preference. At a minimum,
  specify paths to Project-X and remuxTool, specify a directory to output
  transcoded video, and enter your MythTV host IP (if using MythTV).
- If on Linux, optionally install transcode.py to /usr/local/bin and
  copy transcode.conf to ~/.transcode - otherwise, run the program from
  within its directory.

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

# todo -
# 1) simplify encode option parsing (done)
# 2) symlink / MythVideo integration
# 3) MythLog / error handling
# 4) better job handling
# 5) Tmdb integration for movies (done)
# 6) deinterlace / auto-crop filter

# Changelog:
# 1.3 - support for Matroska / VP8, fixed subtitle sync problems
# 1.2 - better accuracy for commercial clipping, easier configuration
# 1.1 - support for multiple audio streams, Comskip
# 1.0 - initial release

# TODO:
# - better error handling
# - check for adequate disk space on temporary directory and destination
# - generate thumbnail if necessary
# - better genre interpretation for WTV files
# - fetch metadata for movies as well as TV episodes
# - allow users to manually enter in metadata if none can be found

# Long-term goals:
# - add entries to MythTV's database when encoding is finished
# - support for boxed-set TV seasons on DVD
# - metadata / chapter support for as many different players as possible,
#   especially Windows Media Player
# - easier installation: all required programs should be bundled
# - Python 3.x compatibility
# - apply video filters, such as deinterlace, crop detection, etc.
# - a separate program for viewing / editing Comskip data

# Known issues:
# - subtitle font is sometimes too large on QuickTime / iTunes / iPods
# - many Matroska players seem to have trouble displaying metadata properly
# - video_br and video_crf aren't recognized options in ffmpeg 0.7+
# - AtomicParsley can crash on MPEG-4 files larger than 2 GB
# - No Unicode support for AtomicParsley on Windows (Python bug)

import re, os, sys, math, datetime, subprocess, urllib, tempfile, glob
import shutil, codecs, StringIO, time, optparse, unicodedata, logging
import xml.dom.minidom
import MythTV, MythTV.ttvdb.tvdb_api, MythTV.ttvdb.tvdb_exceptions
import tmdb3.tmdb_api, tmdb3.tmdb_exceptions

def _clean(filename):
    'Removes the file if it exists.'
    if filename is None or filename == '':
        return
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

def _convert_timestamp(ts):
    '''Translates the values from a regex match for two timestamps of the
    form 00:12:34,567 into seconds.'''
    start = int(ts.group(1)) * 3600 + int(ts.group(2)) * 60
    start += int(ts.group(3))
    start += float(ts.group(4)) / 10 ** len(ts.group(4))
    end = int(ts.group(5)) * 3600 + int(ts.group(6)) * 60
    end += int(ts.group(7))
    end += float(ts.group(8)) / 10 ** len(ts.group(8))
    return start, end

def _seconds_to_time(sec):
    '''Returns a string representation of the length of time provided.
    For example, 3675.14 -> '01:01:15' '''
    hours = int(sec / 3600)
    sec -= hours * 3600
    minutes = int(sec / 60)
    sec -= minutes * 60
    return '%02d:%02d:%02d' % (hours, minutes, sec)

def _seconds_to_time_frac(sec, comma = False):
    '''Returns a string representation of the length of time provided,
    including partial seconds.
    For example, 3675.14 -> '01:01:15.140000' '''
    hours = int(sec / 3600)
    sec -= hours * 3600
    minutes = int(sec / 60)
    sec -= minutes * 60
    if comma:
        frac = int(round(sec % 1.0 * 1000))
        return '%02d:%02d:%02d,%03d' % (hours, minutes, sec, frac)
    else:
        return '%02d:%02d:%07.4f' % (hours, minutes, sec)

def _levenshtein(lhs, rhs):
    '''Computes the Levenbshtein distance between two strings, as discussed
    and implemented in http://en.wikipedia.org/wiki/Levenshtein_distance'''
    xlen = len(lhs) + 1
    ylen = len(rhs) + 1
    arr = [[0 for col in xrange(0, xlen)] for row in xrange(0, ylen)]
    for y in xrange(0, ylen):
        arr[y][0] = y
    for x in xrange(0, xlen):
        arr[0][x] = x
    for y in xrange(1, ylen):
        for x in xrange(1, xlen):
            dist = arr[y - 1][x - 1]
            if lhs[x - 1] != rhs[y - 1]:
                dist = min(arr[y - 1][x], arr[y][x - 1], arr[y - 1][x - 1]) + 1
            arr[y][x] = dist
    return arr[ylen - 1][xlen - 1]

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

def _filter_xml(data):
    'Filters unnecessary whitespace from the raw XML data provided.'
    regex = '<([^/>]+)>\s*(.+)\s*</([^/>]+)>'
    sub = '<\g<1>>\g<2></\g<3>>'
    return re.sub(regex, sub, data)

def _list_to_utf8(args):
    'Converts a list of objects into UTF-8 strings.'
    out = []
    for arg in args:
        if type(arg) is unicode:
            out.append(arg.encode('utf_8'))
        else:
            out.append(str(arg))
    return out

def _cmd(args, cwd = None, expected = 0):
    '''Executes an external command with the given working directory, ignoring
    all output. Raises a RuntimeError exception if the return code of the
    subprocess isn't what is expected.'''
    args = _list_to_utf8(args)
    ret = 0
    logging.debug('$ %s' % ' '.join(args))
    time.sleep(0.5)
    proc = subprocess.Popen(args, stdout = subprocess.PIPE,
                            stderr = subprocess.STDOUT, cwd = cwd)
    for line in proc.stdout:
        logging.debug(line.replace('\n', ''))
    ret = proc.wait()
    time.sleep(0.5)
    if ret != 0 and ret != expected:
        raise RuntimeError('Unexpected return code', ' '.join(args), ret)
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
                    ret = match.group(1).strip()
                    break
            for line in proc.stdout:
                pass
            proc.wait()
        except OSError:
            pass
    return ret

def _nero_ver():
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

def _ffmpeg_ver():
    '''Determines whether ffmpeg is present, and if so, returns the
    version string for later.'''
    return _ver(['ffmpeg', '-version'], '([Ff]+mpeg.*)$',
                use_stderr = False)

def _x264_ver():
    '''Determines whether x264 is present, and if so, returns the
    version string for later. Does not check whether ffmpeg has libx264
    support linked in.'''
    return _ver(['x264', '--version'], '(x264.*)$')

def _vp8_ver():
    '''Determines whether x264 is present, and if so, returns the
    version string for later. Does not check whether ffmpeg has libx264
    support linked in.'''
    return _ver(['vp8enc'], '(VP8 Encoder .*)$')

def _faac_ver():
    '''Determines whether faac is present, and if so, returns the
    version string for later. Does not check whether ffmpeg has libfaac
    support linked in.'''
    return _ver(['faac', '--help'], '(FAAC.*)$')

def _flac_ver():
    '''Determines whether faac is present, and if so, returns the
    version string for later. Does not check whether ffmpeg has libfaac
    support linked in.'''
    return _ver(['flac', '-version'], '(flac .*)$')

def _projectx_ver(opts):
    '''Determines whether Project-X is present, and if so, returns the
    version string for later.'''
    return _ver(['java', '-jar', opts.projectx, '-?'],
                '(ProjectX [0-9/.]*)')

def _version(opts):
    'Compiles a string representing the versions of the encoding tools.'
    nero_ver = _nero_ver()
    faac_ver = _faac_ver()
    x264_ver = _x264_ver()
    vp8_ver = _vp8_ver()
    flac_ver = _flac_ver()
    ver = _ffmpeg_ver()
    if opts.video == 'vp8' and vp8_ver:
        ver += ', %s' % vp8_ver
    elif opts.video == 'h264' and x264_ver:
        ver += ', %s' % x264_ver
    ver += ', %s' % _projectx_ver(opts)
    if opts.aac_encoder == 'nero' and nero_ver:
        ver += ', %s' % nero_ver
    elif opts.audio == 'flac' and flac_ver:
        ver += ', %s' % flac_ver
    elif opts.aac_encoder == 'faac' and faac_ver:
        ver += ', %s' % faac_ver
    logging.debug('Version string: %s' % ver)
    return ver

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

def _find_conf_file():
    'Obtains the location of the config file if one exists.'
    local_dotfile = os.path.expanduser('~/.transcode')
    if os.path.exists(local_dotfile):
        return local_dotfile
    for conf_file in ['/usr/local/etc/transcode.conf', '/etc/transcode.conf']:
        if os.path.exists(conf_file):
            return conf_file
    conf_file = os.path.dirname(os.path.realpath(__file__))
    conf_file = os.path.join(conf_file, 'transcode.conf')
    if os.path.exists(conf_file):
        return conf_file
    return None

def _get_defaults():
    'Returns configuration defaults for this program.'
    opts = {'final_path' : '~/Videos', 'tmp' : None, 'format' : '%T/%T - %S',
            'replace_char' : '', 'language' : 'en', 'country' : 'us',
            'host' : '127.0.0.1', 'database' : 'mythconverg',
            'user' : 'mythtv', 'password' : 'mythtv', 'pin' : 0,
            'import_mythtv' : False, 'container' : 'mp4', 'video' : None,
            'audio' : None, 'ipod' : False, 'webm' : False, 'two_pass' : False,
            'h264_rc' : None, 'vp8_rc' : 'vbr', 'video_br' : 1920,
            'video_crf' : 23, 'preset' : None, 'h264_speed' : 'slow',
            'vp8_speed' : '0', 'threads' : 0, 'resolution' : None,
            'aac_encoder' : 'nero', 'audio_q' : 0.55, 'audio_br' : 192,
            'downmix_to_stereo' : False, 'use_db_rating' : True,
            'use_db_descriptions' : False, 'quiet' : False,
            'verbose' : False, 'clip_thresh' : 5,
            'projectx' : 'project-x/ProjectX.jar',
            'remuxtool' : 'remuxTool.jar' }
    opts['.movie'] = {'format' : '%T'}
    opts['.mp4'] = {'video' : 'h264', 'audio' : 'aac'}
    opts['.mkv'] = {'video' : 'vp8', 'audio' : 'vorbis'}
    opts['.one_pass'] = {'h264_rc' : 'crf'}
    opts['.two_pass'] = {'h264_rc' : 'cbr'}
    opts['.ipod'] = {'container' : 'mp4', 'video' : 'h264', 'audio' : 'aac',
                     'preset' : 'ipod640', 'resolution' : '480p'}
    opts['.webm'] = {'container' : 'mkv', 'video' : 'vp8', 'audio' : 'vorbis'}
    opts['.h264'] = {}
    opts['.vp8'] = {}
    opts['.aac'] = {}
    opts['.vorbis'] = {}
    opts['.flac'] = {}
    opts['.faac'] = {}
    opts['.nero'] = {}
    opts['.ffmpeg-aac'] = {}
    return opts

def _add_option(opts, key, val):
    'Inserts the given configuration setting into the dictionary.'
    dct = opts
    origkey = key
    key = key.lower()
    match = re.search('(\w+)\.(\w+)', key)
    if match:
        dct = opts['.%s' % match.group(2)]
        key = match.group(1)
    if key in ['tmp', 'video', 'audio', 'h264_rc', 'vp8_rc', 'preset',
               'h264_speed', 'vp8_speed', 'resolution']:
        if val == '' or not val:
            val = None
    if key in ['import_mythtv', 'ipod', 'webm', 'two_pass',
               'downmix_to_stereo', 'use_db_rating',
               'use_db_descriptions', 'quiet', 'verbose']:
        val = val.lower()
        if val in ['1', 't', 'y', 'true', 'yes', 'on']:
            val = True
        elif val in ['0', 'f', 'n', 'false', 'no', 'off']:
            val = False
        else:
            raise ValueError('Invalid boolean value for %s: %s' %
                             (origkey, val))
    if key in ['pin', 'video_br', 'video_crf', 'threads',
               'audio_br', 'audio_q', 'clip_thresh']:
        try:
            if key == 'audio_q':
                val = float(val)
            else:
                val = int(val)
        except ValueError:
            raise ValueError('Invalid numerical value for %s: %s' %
                             (origkey, val))
    if key in ['projectx', 'remuxtool']:
        if not os.path.exists(os.path.expanduser(val)):
            raise IOError('File not found: %s' % val)
    dct[key] = val

def _read_options():
    'Reads configuration settings from a file.'
    opts = _get_defaults()
    conf_name = _find_conf_file()
    if conf_name is not None:
        with open(conf_name, 'r') as conf_file:
            regex = re.compile('^\s*(.*)\s*=\s*(.*)\s*$')
            ignore = re.compile('#.*')
            for line in conf_file:
                line = re.sub(ignore, '', line).strip()
                match = re.search(regex, line)
                if match:
                    _add_option(opts, match.group(1).strip(),
                                match.group(2).strip())
    return opts

def _def_str(test, val):
    'Returns " [default]" if test is equal to val.'
    if test == val:
        return ' [default]'
    else:
        return ''

def _get_options(opts):
    'Uses optparse to obtain command-line options.'
    usage = 'usage: %prog [options] chanid time\n' + \
        '  %prog [options] wtv-file'
    version = '%prog 1.3'
    parser = optparse.OptionParser(usage = usage, version = version,
                                   formatter = optparse.TitledHelpFormatter())
    flopts = optparse.OptionGroup(parser, 'File options')
    flopts.add_option('-o', '--out', dest = 'final_path', metavar = 'PATH',
                      default = opts['final_path'], help = 'directory to ' +
                      'store encoded video file                          ' +
                      '[default: %default]')
    if opts['tmp']:
        flopts.add_option('-t', '--tmp', dest = 'tmp', metavar = 'PATH',
                          default = opts['tmp'], help = 'temporary ' +
                          'directory to be used while transcoding ' +
                          '[default: %default]')
    else:
        flopts.add_option('-t', '--tmp', dest = 'tmp', metavar = 'PATH',
                          help = 'temporary directory to be used while ' +
                          'transcoding [default: %s]' % tempfile.gettempdir())
    flopts.add_option('--format', dest = 'format',
                      default = opts['format'], metavar = 'FMT',
                      help = 'format string for the encoded video filename ' +
                      '          [default: %default]')
    flopts.add_option('--replace', dest = 'replace_char',
                      default = opts['replace_char'],  metavar = 'CHAR',
                      help = 'character to substitute for invalid filename ' +
                      'characters [default: "%default"]')
    flopts.add_option('-l', '--lang', dest = 'language',
                      default = opts['language'], metavar = 'LANG',
                      help = 'two-letter language code [default: %default]')
    flopts.add_option('--country', dest = 'country',
                      default = opts['country'], metavar = 'COUNTRY',
                      help = 'two-letter country code for TMDb ' +
                      '[default: %default]')
    parser.add_option_group(flopts)
    myopts = optparse.OptionGroup(parser, 'MythTV options')
    myopts.add_option('--host', dest = 'host', metavar = 'IP',
                      default = opts['host'], help = 'MythTV database ' +
                      'host [default: %default]')
    myopts.add_option('--database', dest = 'database', metavar = 'DB',
                      default = opts['database'], help = 'MySQL database ' +
                      'for MythTV [default: %default]')
    myopts.add_option('--user', dest = 'user', metavar = 'USER',
                      default = opts['user'], help = 'MySQL username for ' +
                      'MythTV [default: %default]')
    myopts.add_option('--password', dest = 'password', metavar = 'PWD',
                      default = opts['password'], help = 'MySQL password ' +
                      'for MythTV [default: %default]')
    myopts.add_option('--pin', dest = 'pin', metavar = 'PIN', type = 'int',
                      default = opts['pin'], help = 'MythTV security PIN ' +
                      '[default: %04d]' % opts['pin'])
    myopts.add_option('--import', dest = 'import_mythtv',
                      action = 'store_true', default = opts['import_mythtv'],
                      help = 'import the transcoded video into MythTV' +
                      _def_str(opts['import_mythtv'], True))
    myopts.add_option('--no-import', dest = 'import_mythtv',
                      action = 'store_false', help = 'don\'t import ' +
                      'video into MythTV' +
                      _def_str(opts['import_mythtv'], False))
    parser.add_option_group(myopts)
    vfopts = optparse.OptionGroup(parser, 'Video format options')
    vfopts.add_option('--container', dest = 'container', metavar = 'FMT',
                      default = opts['container'], choices = ['mp4', 'mkv'],
                      help = 'the media container file type to use ' +
                      '[default: %default]')
    vfopts.add_option('--video', dest = 'video', metavar = 'CODEC',
                      default = opts['video'], choices = ['h264', 'vp8'],
                      help = 'the codec to use for encoding video ' +
                      '[default: %default]')
    vfopts.add_option('--audio', dest = 'audio', metavar = 'CODEC',
                      default = opts['audio'],
                      choices = ['aac', 'vorbis', 'flac'], help = 'the ' +
                      'codec to use for encoding audio [default: %default]')
    vfopts.add_option('--ipod', dest = 'ipod', action = 'store_true',
                      default = opts['ipod'], help = 'use iPod Touch ' +
                      'compatibility settings' + _def_str(opts['ipod'], True))
    vfopts.add_option('--no-ipod', dest = 'ipod', action = 'store_false',
                      help = 'do not use iPod compatibility settings' +
                      _def_str(opts['ipod'], False))
    vfopts.add_option('--webm', dest = 'webm', action = 'store_true',
                      default = opts['webm'], help = 'encode WebM ' +
                      'compliant video' + _def_str(opts['webm'], True))
    vfopts.add_option('--no-webm', dest = 'webm', action = 'store_false',
                      help = 'do not encode WebM compliant video' +
                      _def_str(opts['webm'], False))
    parser.add_option_group(vfopts)
    viopts = optparse.OptionGroup(parser, 'Video encoding options')
    viopts.add_option('-1', '--one-pass', dest = 'two_pass',
                      action = 'store_false', default = opts['two_pass'],
                      help = 'one-pass encoding' +
                      _def_str(opts['two_pass'], False))
    viopts.add_option('-2', '--two-pass', dest = 'two_pass',
                      action = 'store_true', help = 'two-pass encoding' +
                      _def_str(opts['two_pass'], True))
    viopts.add_option('--h264-rc', dest = 'h264_rc', metavar = 'RC',
                      default = opts['h264_rc'], choices = ['crf', 'cbr'],
                      help = 'x264 ratecontrol method to use ' +
                      '[default: %default]')
    viopts.add_option('--vp8-rc', dest = 'vp8_rc', metavar = 'RC',
                      default = opts['vp8_rc'], choices = ['vbr', 'cbr'],
                      help = 'libvpx ratecontrol method to use ' +
                      '[default: %default]')
    viopts.add_option('--video-br', dest = 'video_br', metavar = 'BR',
                      type = 'int', default = opts['video_br'],
                      help = 'target video bitrate (in KB/s) ' +
                      '[default: %default]')
    viopts.add_option('--video-crf', dest = 'video_crf', metavar = 'CR',
                      type = 'int', default = opts['video_crf'],
                      help = 'target H.264 video quality ratio (15 to 25 ' +
                      'is ideal) [default: %default]')
    viopts.add_option('--preset', dest = 'preset', metavar = 'PRE',
                      default = opts['preset'], help = 'ffmpeg preset ' +
                      'file to use [default: %default]')
    viopts.add_option('--h264-speed', dest = 'h264_speed', metavar = 'SP',
                      choices = ['slow', 'medium', 'fast', 'faster'],
                      default = opts['h264_speed'], help = 'x264 encoding ' +
                      'speed [default: %default]')
    viopts.add_option('--vp8-speed', dest = 'vp8_speed', metavar = 'SP',
                      choices = [str(x) for x in xrange(0, 7)],
                      default = opts['vp8_speed'], help = 'libvpx encoding ' +
                      'speed [default: %default]')
    viopts.add_option('--threads', dest = 'threads', metavar = 'TH',
                      type = 'int', default = opts['threads'],
                      help = 'amount of concurrent threads of execution ' +
                      'to use when transcoding video [default: %default]')
    viopts.add_option('-r', '--resolution', dest = 'resolution',
                      metavar = 'RES', default = opts['resolution'],
                      help = 'target video resolution or aspect ratio ' +
                      '[default: %default]')
    parser.add_option_group(viopts)
    auopts = optparse.OptionGroup(parser, 'Audio encoding options')
    auopts.add_option('--aac-encoder', dest = 'aac_encoder', metavar = 'ENC',
                      choices = ['faac', 'nero', 'ffmpeg-aac'],
                      default = opts['aac_encoder'], help = 'the encoder to ' +
                      'use for AAC audio [default: %default]')
    auopts.add_option('--audio-q', dest = 'audio_q', metavar = 'Q',
                      type = 'float', default = opts['audio_q'], help =
                      'neroAacEnc audio quality ratio [default: %default]')
    auopts.add_option('--audio-br', dest = 'audio_br', metavar = 'BR',
                      type = 'int', default = opts['audio_br'], help =
                      'libfaac, ffmpeg-aac or vorbis audio bitrate ' +
                      '(in KB/s) [default: %default]')
    auopts.add_option('--stereo', dest = 'downmix_to_stereo',
                      action = 'store_true',
                      default = opts['downmix_to_stereo'],
                      help = 'downmix 5.1 surround sound to two channels' +
                      _def_str(opts['downmix_to_stereo'], True))
    parser.add_option_group(auopts)
    mdopts = optparse.OptionGroup(parser, 'Metadata options')
    mdopts.add_option('--rating', dest = 'use_db_rating',
                      action = 'store_true', default = opts['use_db_rating'],
                      help = 'include Tvdb / TMDb rating (1 to 10) ' +
                      'as voted by users' +
                      _def_str(opts['use_db_rating'], True))
    mdopts.add_option('--no-rating', dest = 'use_db_rating',
                      action = 'store_false', help = 'do not include Tvdb / ' +
                      'Tmdb rating' +
                      _def_str(opts['use_db_rating'], False))
    mdopts.add_option('--db-description', dest = 'use_db_descriptions',
                      action = 'store_true',
                      default = opts['use_db_descriptions'], help = 'use ' +
                      'episode / movie descriptions from Tvdb / TMDb ' +
                      'when available' +
                      _def_str(opts['use_db_descriptions'], True))
    parser.add_option_group(mdopts)
    miopts = optparse.OptionGroup(parser, 'Miscellaneous options')
    miopts.add_option('-q', '--quiet', dest = 'quiet', action = 'store_true',
                      default = opts['quiet'], help = 'avoid printing to ' +
                      'stdout' + _def_str(opts['quiet'], True))
    miopts.add_option('-v', '--verbose', dest = 'verbose',
                      action = 'store_true', default = opts['verbose'],
                      help = 'print command output to stdout' +
                      _def_str(opts['verbose'], True))
    miopts.add_option('--thresh', dest = 'clip_thresh', metavar = 'TH',
                      type = 'int', default = opts['clip_thresh'],
                      help = 'ignore clip segments TH seconds from the ' +
                      'beginning or end [default: %default]')
    miopts.add_option('--project-x', dest = 'projectx', metavar = 'PATH',
                      default = opts['projectx'], help = 'path to the ' +
                      'Project-X JAR file                            ' +
                      '(used for noise cleaning / cutting)')
    miopts.add_option('--remuxtool', dest = 'remuxtool', metavar = 'PATH',
                      default = opts['remuxtool'], help = 'path to ' +
                      'remuxTool.jar                               ' +
                      '(used for extracting MPEG-2 data from WTV files)')
    parser.add_option_group(miopts)
    return parser

def _collapse_args(defaults, opts):
    '''Applies the options in a subgroup to global options if the condition
    for that subgroup is met.'''
    groups = [('mp4', 'container'), ('mkv', 'container'),
              ('h264', 'video'), ('vp8', 'video'), ('aac', 'audio'),
              ('vorbis', 'audio'), ('flac', 'audio'), ('ipod', 'ipod'),
              ('webm', 'webm'), ('one_pass', 'two_pass'),
              ('two_pass', 'two_pass'), ('faac', 'aac_encoder'),
              ('nero', 'aac_encoder'), ('ffmpeg-aac', 'aac_encoder')]
    for group, condition in groups:
        cond = getattr(opts, condition)
        if group == 'one_pass':
            cond = not cond
        if cond is True or cond == group:
            for key, val in defaults['.%s' % group].iteritems():
                setattr(opts, key, val)

def _check_args(args, parser, opts):
    '''Checks to ensure the positional arguments are valid, and adjusts
    conflicting options if necessary.'''
    if len(args) == 2:
        try:
            ts = _convert_time(args[1])
        except ValueError:
            print 'Error: invalid timestamp.'
            exit(1)
    elif len(args) == 1 and not args[0].isdigit():
        args[0] = os.path.expanduser(args[0])
        if not os.path.exists(args[0]):
            print 'Error: file not found.'
            exit(1)
        wtv = re.search('\.[Ww][Tt][Vv]', args[0])
        mp4 = re.search('\.[Mm][Pp]4', args[0])
        m4v = re.search('\.[Mm]4[Vv]', args[0])
        mkv = re.search('\.[Mm][Kk][Vv]', args[0])
        if not (wtv or mp4 or m4v or mkv):
            print 'Error: file is not a WTV recording or a valid video file.'
            exit(1)
    else:
        parser.print_help()
        exit(1)
    if opts.final_path in [None, '', '.', './', '.\\']:
        opts.final_path = os.path.dirname(os.path.realpath(__file__))
    for key in ['final_path', 'tmp', 'projectx', 'remuxtool']:
        if getattr(opts, key) is not None:
            setattr(opts, key, os.path.expanduser(getattr(opts, key)))
    if opts.ipod and opts.webm:
        print 'Error: WebM and iPod options conflict.'
        exit(1)
    loglvl = logging.INFO
    if opts.verbose:
        loglvl = logging.DEBUG
    if opts.quiet:
        loglvl = logging.CRITICAL
    logging.basicConfig(format = '%(message)s', level = loglvl)

class Subtitles:
    '''Extracts closed captions from source media using ccextractor and
    writes them as SRT timed-text subtitles.'''
    subs = 1
    marks = []
    
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
        return ver is not None and not self.source.opts.webm
    
    def mark(self, sec):
        'Marks a cutpoint in the video at a given point.'
        self.marks += [sec]
    
    def extract(self, video):
        '''Obtains the closed-caption data embedded as VBI data within the
        filtered video clip and writes them to a SRT file.'''
        if not self.enabled:
            return
        logging.info('*** Extracting subtitles ***')
        _cmd(['ccextractor', '-o', self.srt, '-utf8', '-ve',
              '--no_progress_bar', video], expected = 232)
    
    def adjust(self):
        '''Joining video can cause the closed-caption VBI data to become
        out-of-sync with the video, because some closed captions last longer
        than the individual clips and ccextractor doesn't know when to clip
        these captions. To compensate for this, any captions which
        extend longer than the cutpoint are clipped, and the difference is
        subtracted from the rest of the captions.'''
        if len(self.marks) == 0:
            return
        delay = 0.0
        curr = 0
        newsubs = ''
        ts = '(\d\d):(\d\d):(\d\d),(\d+)'
        regex = re.compile(ts + '\s*-+>\s*' + ts)
        with open(self.srt, 'r') as subs:
            for line in subs:
                match = re.search(regex, line)
                if match:
                    start, end = _convert_timestamp(match)
                    start += delay
                    end += delay
                    if curr < len(self.marks) and self.marks[curr] < end:
                        if self.marks[curr] > start:
                            delay += self.marks[curr] - end
                            end = self.marks[curr]
                        curr += 1
                    start = _seconds_to_time_frac(start, True)
                    end = _seconds_to_time_frac(end, True)
                    newsubs += '%s --> %s\n' % (start, end)
                else:
                    newsubs += line
        _clean(self.srt)
        with open(self.srt, 'w') as subs:
            subs.write(newsubs)
    
    def clean_tmp(self):
        'Removes temporary SRT files.'
        _clean(self.srt)

class MP4Subtitles(Subtitles):
    'Embeds SRT subtitles into the final MPEG-4 video file.'
    
    def write(self):
        'Invokes MP4Box to embed the SRT subtitles into a MP4 file.'
        if not self.enabled:
            return
        arg = '%s:name=Subtitles:layout=0x125x0x-1' % self.srt
        _cmd(['MP4Box', '-tmp', self.source.opts.final_path, '-add',
              arg, self.source.final_file])

class MKVSubtitles(Subtitles):
    'Embeds SRT subtitles into the final MPEG-4 video file.'
    
    def write(self):
        '''Returns command-line arguments for mkvmerge to embed the SRT
        subtitles into a MKV file.'''
        return ['--track-name', '0:Subtitles', self.srt]

class MP4Chapters:
    'Creates iOS-style chapter markers between designated cutpoints.'
    
    def __init__(self, source):
        self.source = source
        self.enabled = not self.source.opts.webm
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
        if not self.enabled:
            return
        _clean(self._chap)
        data = self._doc.toprettyxml(encoding = 'UTF-8', indent = '  ')
        data = _filter_xml(data)
        logging.debug('Chapter XML file:')
        logging.debug(data)
        with open(self._chap, 'w') as dest:
            dest.write(data)
        args = ['MP4Box', '-tmp', self.source.opts.final_path,
                '-add', '%s:chap' % self._chap, self.source.final_file]
        try:
            _cmd(args)
        except RuntimeError:
            logging.warning('*** Old version of MP4Box, ' +
                            'chapter support unavailable ***')
    
    def clean_tmp(self):
        'Removes the temporary chapter XML file.'
        _clean(self._chap)

class MKVChapters:
    '''Creates a simple-format Matroska chapter file and embeds it into
    the final MKV media file.'''
    
    def __init__(self, source):
        self.source = source
        self.enabled = not source.opts.webm
        self._chap = source.base + '.chap'
        self._data = ''
    
    def add(self, pos, seg):
        '''Adds a new chapter marker at pos (in seconds).
        If seg is provided, the marker will be labelled 'Scene seg+1'.'''
        if seg is None or not self.enabled:
            return
        time = _seconds_to_time_frac(pos)
        self._data += 'CHAPTER%02d=%s\n' % (seg, time)
        self._data += 'CHAPTER%02dNAME=%s\n' % (seg, 'Scene %d' % (seg + 1))
    
    def write(self):
        '''Writes the chapter file and returns command-line arguments to embed
        the chapter date into a MKV file.'''
        if not self.enabled:
            return []
        _clean(self._chap)
        logging.debug('Chapter data file:')
        logging.debug(self._data)
        if len(self._data) > 0:
            with open(self._chap, 'w') as dest:
                dest.write(self._data)
            return ['--chapters', self._chap]
        else:
            return []
    
    def clean_tmp(self):
        'Removes the temporary chapter file.'
        _clean(self._chap)

class MP4Metadata:
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
            return not self.source.opts.webm
        else:
            return False
    
    def _get_director(self):
        '''Browses through the credits tuple and returns the first credited
        director encountered.'''
        if self.source.get('credits') is not None:
            for person in self.source.get('credits'):
                if person[1] == 'director':
                    return person[0]
        return None
    
    def _sort_credits(self):
        '''Browses through the previously obtained list of credited people
        involved with the episode and returns three separate lists of
        actors/hosts/guest stars, directors, and producers/writers.'''
        cast = []
        directors = []
        producers = []
        writers = []
        c = self.source.get('credits')
        for person in c:
            if person[1] in ['actor', 'host', '']:
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
                writers.append(person[0])
            if person[1] == 'screenwriter':
                writers.append(person[0])
        return cast, directors, producers, writers
    
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
        (cast, directors, producers, writers) = self._sort_credits()
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
        self._make_section(writers, 'screenwriters', top, doc)
        return doc
    
    def _perform(self, args):
        '''Invokes AtomicParsley with the provided command-line arguments. If
        the program is successful and outputs a new MP4 file with the newly
        embedded metadata, copies the new file over the old.'''
        self.clean_tmp()
        args = ['AtomicParsley', self.source.final_file] + args
        _cmd(args)
        for old in glob.glob(self.source.final + '-temp-*.' +
                             self.source.ext):
            shutil.move(old, self.source.final_file)
    
    def _simple_tags(self, version):
        'Adds single-argument or standalone tags into the MP4 file.'
        s = self.source
        if s.get('movie') is True:
            args = ['--stik', 'Movie', '--encodingTool', version]
        else:
            args = ['--stik', 'TV Show', '--encodingTool', version]
        if type(s) == WTVSource:
            args += ['--grouping', 'Windows Media Center Recording']
        elif type(s) == MythSource:
            args += ['--grouping', 'MythTV Recording']
        if s.get('time') is not None:
            utc = s.time.strftime('%Y-%m-%dT%H:%M:%SZ')
            args += ['--purchaseDate', utc]
        if s.get('title') is not None:
            t = s['title']
            if s.get('movie') is not True:
                args += ['--artist', t, '--album', t, '--albumArtist', t,
                         '--TVShowName', t]
            else:
                args += ['--title', t]
                director = self._get_director()
                if director is not None:
                    args += ['--artist', director]
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
        if s.get('tagline') is not None:
            args += ['--comment', s['tagline']]
        self._perform(args)
    
    def _longer_tags(self):
        '''Adds lengthier tags (such as episode description or series artwork)
        into the MP4 file separately, to avoid problems.'''
        s = self.source
        args = []
        if s.get('description') is not None:
            args += ['--description', s['description'][:255]]
            if len(s.get('description')) > 255:
                args += ['--longdesc', s['description']]
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
            logging.info('*** Adding metadata to %s ***'
                         % self.source.final_file)
            self._simple_tags(version)
            self._longer_tags()
            self._credits()
    
    def clean_tmp(self):
        'Removes any leftover MP4 files created by AtomicParsley.'
        files = u'%s-temp-*.%s' % (self.source.final, self.source.ext)
        for old in glob.glob(files):
            _clean(old)

class MKVMetadata:
    '''Translates previously fetched metadata (series name, episode name,
    episode number, credits...) into an XML tags file for mkvmerge
    in order to embed it as Matroska tags.'''
    
    def __init__(self, source):
        self.source = source
        self.enabled = not self.source.opts.webm
        self._tags = self.source.base + '-tags.xml'
        imp = xml.dom.minidom.getDOMImplementation()
        url = 'http://www.matroska.org/files/tags/matroskatags.dtd'
        dt = imp.createDocumentType('Tags', None, url)
        self._doc = imp.createDocument(url, 'Tags', dt)
        self._root = self._doc.documentElement
        self._show = self._make_tag('collection', 70)
        self._season = self._make_tag('season', 60)
        self._ep = self._make_tag('episode', 50)
    
    def _make_tag(self, targtype, targval):
        '''Creates an XML branch for Matroska tags using the desired level
        of specificity to which the included tags will apply.'''
        tag = self._doc.createElement('Tag')
        targ = self._doc.createElement('Targets')
        tv = self._doc.createElement('TargetTypeValue')
        tv.appendChild(self._doc.createTextNode(str(targval)))
        targ.appendChild(tv)
        tt = self._doc.createElement('TargetType')
        tt.appendChild(self._doc.createTextNode(targtype.upper()))
        targ.appendChild(tt)
        tag.appendChild(targ)
        self._root.appendChild(tag)
        return tag
    
    def _add_simple(self, tag, name, val):
        '''Creates an XML Matroska <Simple> tag with the specified name
        and value and attaches it to the given tag.'''
        simple = self._doc.createElement('Simple')
        n = self._doc.createElement('Name')
        n.appendChild(self._doc.createTextNode(name.upper()))
        simple.appendChild(n)
        v = self._doc.createElement('String')
        v.appendChild(self._doc.createTextNode(str(val)))
        simple.appendChild(v)
        tag.appendChild(simple)
    
    def _add_date(self, tag, name, date):
        '''Translates a datetime object into a UTC timestamp and adds it to
        the specified XML tag.'''
        if date is not None:
            self._add_simple(tag, name, date.strftime('%Y-%m-%d'))
    
    def _add_tags(self, version):
        'Adds most simple metadata tags to the XML tree.'
        utc = datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        if self.source.get('title') is not None:
            self._add_simple(self._show, 'title', self.source.get('title'))
        if self.source.get('category') is not None:
            self._add_simple(self._show, 'genre', self.source.get('category'))
        if self.source.get('seasoncount') is not None:
            self._add_simple(self._show, 'part_number',
                             self.source.get('seasoncount'))
        if self.source.get('season') is not None:
            self._add_simple(self._season, 'part_number',
                             self.source.get('season'))
        if self.source.get('episodecount') is not None:
            self._add_simple(self._season, 'total_parts',
                             self.source.get('episodecount'))
        tags = {'subtitle' : 'subtitle', 'episode' : 'part_number',
                'syndicatedepisodenumber' : 'catalog_number',
                'channel' : 'distributed_by', 'description' : 'summary',
                'rating' : 'law_rating'}
        for key, val in tags.iteritems():
            if self.source.get(key) is not None:
                self._add_simple(self._ep, val, self.source.get(key))
        if self.source.get('popularity'):
            popularity = self.source.get('popularity') / 51.0 * 2
            popularity = round(popularity) / 2.0
            self._add_simple(self._ep, 'rating', popularity)
        self._add_date(self._ep, 'date_released',
                       self.source.get('originalairdate'))
        self._add_date(self._ep, 'date_recorded', self.source.time)
        self._add_simple(self._ep, 'date_encoded', utc)
        self._add_simple(self._ep, 'date_tagged', utc)
        self._add_simple(self._ep, 'encoder', version)
        if self.source.fps > 0:
            self._add_simple(self._ep, 'fps', self.source.fps)
    
    def _credits(self):
        'Adds a list of credited people into the XML tree.'
        for person in self.source.get('credits'):
            if person[1] in ['actor', 'host', 'guest_star', '']:
                self._add_simple(self._ep, 'actor', person[0])
            elif person[1] == 'director':
                self._add_simple(self._ep, 'director', person[0])
            elif person[1] == 'executive_producer':
                self._add_simple(self._ep, 'executive_producer', person[0])
            elif person[1] == 'producer':
                self._add_simple(self._ep, 'producer', person[0])
            elif person[1] == 'writer':
                self._add_simple(self._ep, 'written_by', person[0])
            elif person[1] == 'screenwriter':
                self._add_simple(self._ep, 'screenplay_by', person[0])
    
    def write(self, version):
        '''Writes the metadata XML file and returns command-line arguments to
        mkvmerge in order to embed it, along with album artwork if available,
        into the final MKV file.'''
        _clean(self._tags)
        if not self.enabled:
            return []
        logging.info('*** Adding metadata to %s ***' % self.source.final_file)
        self._add_tags(version)
        self._credits()
        data = self._doc.toprettyxml(encoding = 'UTF-8', indent = '  ')
        data = _filter_xml(data)
        logging.debug('Tag XML file:')
        logging.debug(data)
        with open(self._tags, 'w') as dest:
            dest.write(data)
        args = ['--global-tags', self._tags]
        if self.source.get('albumart') is not None:
            if self.source.get('movie'):
                args += ['--attachment-description', 'Movie poster']
            else:
                args += ['--attachment-description', 'Episode preview']
            args += ['--attachment-mime-type', 'image/jpeg']
            args += ['--attach-file', self.source.get('albumart')]
        return args
    
    def clean_tmp(self):
        'Removes the XML tags file if it exists.'
        _clean(self._tags)

class Transcoder:
    '''Base class which invokes tools necessary to extract, split, demux
    and encode the media.'''
    seg = 0
    subtitles = None
    chapters = None
    metadata = None
    _split = []
    _demuxed = []
    _demux_v = None
    _demux_a = None
    _frames = 0
    _extra = 0
    
    def __init__(self, source, opts):
        self.source = source
        self.opts = opts
        self._join = source.base + '-join.ts'
        self._demux = source.base + '-demux'
        self._wav = source.base + '.wav'
        self.video = source.base + '.' + self.opts.video
        if self.opts.audio == 'vorbis':
            self.audio = source.base + '.ogg'
        else:
            self.audio = source.base + '.' + self.opts.audio
        self.check()
    
    def check(self):
        '''Determines whether ffmpeg is installed and has built-in support
        for the requested encoding method.'''
        codecs = ['ffmpeg', '-codecs']
        if not _ffmpeg_ver():
            raise RuntimeError('FFmpeg is not installed.')
        if self.opts.video not in ['h264', 'vp8']:
            raise RuntimeError('No video codec chosen.')
        if (self.opts.video == 'h264' and
            not _ver(codecs, '--enable-(libx264)')):
            raise RuntimeError('FFmpeg does not support libx264.')
        elif (self.opts.video == 'vp8' and
              not _ver(codecs, '--enable-(libvpx)')):
            raise RuntimeError('FFmpeg does not support libvpx.')
        if self.opts.audio not in ['aac', 'vorbis', 'flac']:
            raise RuntimeError('No audio codec chosen.')
        if self.opts.audio == 'aac':
            if self.opts.aac_encoder not in ['nero', 'faac', 'ffmpeg-aac']:
                raise RuntimeError('No AAC encoder chosen.')
            if self.opts.aac_encoder == 'nero' and not _nero_ver():
                raise RuntimeError('neroAacEnc is not installed.')
            elif (self.opts.aac_encoder == 'faac' and
                  not _ver(codecs, '--enable-(libfaac)')):
                raise RuntimeError('FFmpeg does not support libfaac.')
            elif (self.opts.aac_encoder == 'ffmpeg-aac' and
                  not _ver(codecs, 'EA.*(aac)\s+')):
                raise RuntimeError('FFmpeg does not support ffmpeg-aac.')
        elif self.opts.audio == 'flac' and not _ver(codecs, 'EA.*(flac)\s+'):
            raise RuntimeError('FFmpeg does not support FLAC.')
        elif (self.opts.audio == 'vorbis' and
              not _ver(codecs, '--enable-(libvorbis)')):
            raise RuntimeError('FFmpeg does not support libvorbis.')
        if not self.source.meta_present:
            self.metadata.enabled = False
    
    def _extract(self, clip, elapsed):
        '''Creates a new chapter marker at elapsed and uses ffmpeg to extract
        an MPEG-TS video clip from clip[0] to clip[1]. All values are
        in seconds.'''
        logging.info('*** Extracting segment %d: [%s - %s] ***' %
                     (self.seg + 1, _seconds_to_time(clip[0]),
                      _seconds_to_time(clip[1])))
        self.chapters.add(elapsed, self.seg)
        args = ['ffmpeg', '-y', '-i', self.source.orig, '-ss', str(clip[0]),
                '-t', str(clip[1] - clip[0])] + self.source.split_args[0]
        split = '%s-%d.ts' % (self.source.base, self.seg)
        args += [split]
        self._split += split
        if len(self.source.split_args) > 1:
            args += self.source.split_args[1]
        _cmd(args)
        self.seg += 1
        self.subtitles.mark(clip[1])
    
    def split(self):
        '''Uses the source's cutlist to mark specific video clips from the
        source video for extraction while also setting chapter markers.'''
        (pos, elapsed) = (0, 0)
        for cut in self.source.cutlist:
            (start, end) = cut
            if start > self.opts.clip_thresh and start > pos:
                self._extract((pos, start), elapsed)
            elapsed += start - pos
            pos = end
        if pos < self.source.duration - self.opts.clip_thresh:
            self._extract((pos, self.source.duration), elapsed)
            elapsed += self.source.duration - pos
            pos = self.source.duration
        self.chapters.add(elapsed, None)
    
    def join(self):
        '''Uses ffmpeg's concat: protocol to rejoin the previously split
        video clips, and then extracts subtitles from the resulting video.'''
        logging.info('*** Joining video to %s ***' % self._join)
        self.subtitles.clean_tmp()
        concat = 'concat:'
        for seg in xrange(0, self.seg):
            name = '%s-%d.ts' % (self.source.base, seg)
            if os.path.exists(name):
                concat += '%s|' % name
            else:
                raise RuntimeError('Could not find video segment %s.' % name)
        concat = concat[:-1]
        args = ['ffmpeg', '-y', '-i', concat] + self.source.split_args[0]
        args += [self._join]
        if len(self.source.split_args) > 1:
            args += self.source.split_args[1]
        _cmd(args)
        self.subtitles.extract(self._join)
        self.subtitles.adjust()
    
    def _find_streams(self):
        '''Locates the PID numbers of the video and audio streams to be encoded
        using ffmpeg.'''
        (vstreams, astreams) = ([], [])
        stream = 'Stream.*\[0x([0-9a-fA-F]+)\].*'
        videoRE = re.compile(stream + 'Video:.*\s+([0-9]+)x([0-9]+)')
        audioRE = re.compile(stream + ':\s*Audio')
        proc = subprocess.Popen(['ffmpeg', '-i', self._join],
                                stdout = subprocess.PIPE,
                                stderr = subprocess.STDOUT)
        for line in proc.stdout:
            match = re.search(videoRE, line)
            if match:
                enabled = False
                if re.search('Video:.*\(Main\)', line):
                    logging.debug('Found video stream 0x%s' %
                                  match.group(1))
                    enabled = True
                vstreams += [(int(match.group(1), 16), enabled)]
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
            proc.wait()
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
        return vstreams, astreams
    
    def _find_demux(self):
        'Uses the Project-X log to obtain the separated video / audio files.'
        (vstreams, astreams) = self._find_streams()
        with open('%s_log.txt' % self._demux, 'r') as log:
            videoRE = re.compile('Video: PID 0x([0-9A-Fa-f]+)')
            audioRE = re.compile('Audio: PID 0x([0-9A-Fa-f]+)')
            fileRE = re.compile('\'(.*)\'\s*$')
            curr_v, curr_a = 1, 1
            found_v, found_a = 0, 0
            targ_v, targ_a = 0, 0
            for line in log:
                match = re.search(videoRE, line)
                if match:
                    found_v += 1
                    pid = int(match.group(1), 16)
                    for vid in vstreams:
                        if vid[0] == pid and vid[1]:
                            targ_v = found_v
                match = re.search(audioRE, line)
                if match:
                    found_a += 1
                    pid = int(match.group(1), 16)
                    for aud in astreams:
                        if aud[0] == pid and aud[1]:
                            targ_a = found_a
                if re.match('\.Video ', line):
                    match = re.search(fileRE, line)
                    if match:
                        self._demuxed += match.group(1)
                        if curr_v == targ_v:
                            self._demux_v = match.group(1)
                    curr_v += 1
                elif re.match('Audio \d', line):
                    match = re.search(fileRE, line)
                    if match:
                        self._demuxed += match.group(1)
                        if curr_a == targ_a:
                            self._demux_a = match.group(1)
                    curr_a += 1
    
    def demux(self):
        '''Invokes Project-X to clean noise from raw MPEG-2 video capture data,
        split the media along previously specified cutpoints and combine into
        one file, and then extract each media stream (video / audio) from the
        container into separate raw data files.'''
        logging.info('*** Demuxing video ***')
        name = os.path.basename(self._demux)
        try:
            _cmd(['java', '-jar', self.opts.projectx, '-out', self.opts.tmp,
                  '-name', name, '-demux', self._join])
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
        '''Adjusts the resolution of the transcoded video to be exactly the
        desired target resolution (if one is chosen), preserving aspect ratio
        by padding extra space with black pixels.'''
        size = []
        res = self.source.resolution
        target = self.opts.resolution
        if target is not None:
            aspect = res[0] * 1.0 / res[1]
            if aspect > target[0] * 1.0 / target[1]:
                vres = int(round(target[0] / aspect))
                if vres % 2 == 1:
                    vres += 1
                pad = (target[1] - vres) / 2
                size = ['-s', '%dx%d' % (target[0], vres), '-vf',
                        'pad=%d:%d:0:%d:black' % (target[0], target[1], pad)]
            else:
                hres = int(round(target[1] * aspect))
                if hres % 2 == 1:
                    hres += 1
                pad = (target[0] - hres) / 2
                size = ['-s', '%dx%d' % (hres, target[1]), '-vf',
                        'pad=%d:%d:%d:0:black' % (target[0], target[1], pad)]
        return size
    
    def encode_video(self):
        'Invokes ffmpeg to transcode the video stream to H.264 or VP8.'
        preset, threads, rate, speed = [], [], [], []
        fmt, codec = '', ''
        if self.opts.preset:
            preset = ['-vpre', self.opts.preset]
        if self.opts.video == 'vp8':
            fmt, codec = 'matroska', 'libvpx'
            if self.opts.webm:
                fmt, codec = 'webm', 'libvpx'
            if self.opts.vp8_rc == 'vbr':
                rate = ['-vb', '%dk' % self.opts.video_br]
            elif self.opts.vp8_rc == 'cbr':
                r = '%dk' % self.opts.video_br
                rate = ['-minrate', r, '-maxrate', r, '-vb', r]
            if self.opts.vp8_speed is not None:
                speed = ['-speed', self.opts.vp8_speed]
        elif self.opts.video == 'h264':
            fmt, codec = 'mp4', 'libx264'
            if self.opts.ipod:
                fmt, codec = 'ipod', 'libx264'
            if self.opts.h264_rc == 'crf':
                rate = ['-crf', self.opts.video_crf]
            elif self.opts.h264_rc == 'cbr':
                rate = ['-vb', '%dk' % self.opts.video_br]
            if self.opts.h264_speed is not None:
                speed = ['-preset', self.opts.h264_speed]
        if self.opts.threads is not None:
            threads = ['-threads', self.opts.threads]
        _clean(self.video)
        size = self._adjust_res()
        common = ['ffmpeg', '-y', '-i', self._demux_v, '-vcodec', codec,
                  '-an', '-f', fmt]
        common += preset + rate + speed + size + threads
        if self.opts.two_pass:
            logging.info(u'*** Encoding video to %s - first pass ***' %
                         self.opts.tmp)
            _cmd(common + ['-pass', 1, os.devnull], cwd = self.opts.tmp)
            logging.info(u'*** Encoding video to %s - second pass ***' %
                         self.video)
            _cmd(common + ['-pass', 2, self.video], cwd = self.opts.tmp)
        else:
            logging.info(u'*** Encoding video to %s ***' % self.video)
            _cmd(common + [self.video])
    
    def encode_audio(self):
        '''Invokes ffmpeg or neroAacEnc to transcode the audio stream to
        AAC, Vorbis or FLAC.'''
        fmt, codec = '', ''
        channels = []
        if self.opts.audio == 'flac':
            fmt, codec = 'flac', 'flac'
        elif self.opts.audio == 'vorbis':
            fmt, codec = 'ogg', 'libvorbis'
        elif self.opts.audio == 'aac':
            fmt = 'aac'
            if self.opts.aac_encoder == 'faac':
                codec = 'libfaac'
            elif self.opts.aac_encoder == 'ffmpeg-aac':
                codec = 'aac'
        if self.opts.downmix_to_stereo and self.source.surround:
            channels = ['-ac', 2]
        _clean(self.audio)
        logging.info(u'*** Encoding audio to %s ***' % self.audio)
        if self.opts.audio == 'aac' and self.opts.aac_encoder == 'nero':
            _cmd(['ffmpeg', '-y', '-i', self._demux_a, '-vn', '-acodec',
                  'pcm_s16le', '-f', 'wav'] + channels + [self._wav])
            _cmd(['neroAacEnc', '-q', self.opts.audio_q, '-if', self._wav,
                  '-of', self.audio])
        else:
            _cmd(['ffmpeg', '-y', '-i', self._demux_a, '-vn', '-acodec',
                  codec, '-ab', '%dk' % self.opts.audio_br, '-f', fmt]
                 + channels + [self.audio])
    
    def clean_video(self):
        'Removes the temporary video stream data.'
        _clean(self._demux_v)
    
    def clean_audio(self):
        'Removes the temporary audio stream data.'
        _clean(self._demux_a)
    
    def clean_split(self):
        'Removes temporary video clips used before rejoining.'
        for split in self._split:
            _clean(split)
    
    def clean_join(self):
        'Removes the temporary rejoined MPEG-2 video data.'
        _clean(self._join)
    
    def clean_tmp(self):
        'Removes any temporary files generated during encoding.'
        self.clean_video()
        self.clean_audio()
        self.clean_split()
        self.clean_join()
        for demux in self._demuxed:
            _clean(demux)
        _clean(self._wav)
        _clean(self.video)
        _clean(self.audio)
        for log in ['ffmpeg2pass-0.log', 'x264_2pass.log',
                    'x264_2pass.log.mbtree', '%s_log.txt' % self._demux,
                    '%s_log.txt' % self.source.base]:
            _clean(os.path.join(self.opts.tmp, log))

class MP4Transcoder(Transcoder):
    'Remuxes and finalizes MPEG-4 media files.'
    
    def __init__(self, source, opts):
        Transcoder.__init__(self, source, opts)
        self.subtitles = MP4Subtitles(source)
        self.chapters = MP4Chapters(source)
        self.metadata = MP4Metadata(source)
        self.check()
    
    def check(self):
        'Determines whether MP4Box is installed.'
        if not _ver(['MP4Box', '-version'], 'version\s*([0-9.DEV]+)'):
            raise RuntimeError('MP4Box is not installed.')
        if not self.source.meta_present:
            self.metadata.enabled = False
    
    def remux(self):
        '''Invokes MP4Box to combine the audio, video and subtitle streams
        into the MPEG-4 target file, also embedding chapter data and
        metadata.'''
        logging.info(u'*** Remuxing to %s ***' % self.source.final_file)
        self.source.make_final_dir()
        _clean(self.source.final_file)
        common = ['MP4Box', '-tmp', self.opts.final_path]
        _cmd(common + ['-new', '-add', '%s#video:name=Video' % self.video,
                       '-add', '%s#audio:name=Audio' % self.audio,
                       self.source.final_file])
        _cmd(common + ['-isma', '-hint', self.source.final_file])
        self.subtitles.write()
        self.chapters.write()
        _cmd(common + ['-lang', self.opts.language, self.source.final_file])
        self.metadata.write(_version(self.opts))
    
    def clean_tmp(self):
        'Removes any temporary files generated during encoding.'
        Transcoder.clean_tmp(self)
        self.subtitles.clean_tmp()
        self.chapters.clean_tmp()
        self.metadata.clean_tmp()

class MKVTranscoder(Transcoder):
    'Remuxes and finalizes Matroska media files.'
    
    def __init__(self, source, opts):
        Transcoder.__init__(self, source, opts)
        self.subtitles = MKVSubtitles(source)
        self.chapters = MKVChapters(source)
        self.metadata = MKVMetadata(source)
        self.check()
    
    def check(self):
        'Determines whether mkvmerge is installed.'
        if not _ver(['mkvmerge', '--version'], '\sv*([0-9.]+)'):
            raise RuntimeError('mkvmerge is not installed.')
        if not self.source.meta_present:
            self.metadata.enabled = False
    
    def remux(self):
        '''Invokes mkvmerge to combine the audio, video and subtitle streams
        into the Matroska target file, also embedding chapter data and
        metadata.'''
        logging.info(u'*** Remuxing to %s ***' % self.source.final_file)
        self.source.make_final_dir()
        _clean(self.source.final_file)
        common = ['--no-chapters', '-B', '-T', '-M', '--no-global-tags']
        args = ['mkvmerge']
        args += ['--default-language', _iso_639_2(self.opts.language)]
        args += common + ['-A', '-S', '--track-name', '1:Video', self.video]
        args += common + ['-D', '-S', '--track-name', '0:Audio', self.audio]
        subs = self.subtitles.write()
        if len(subs) > 0:
            args += common + ['-A', '-D'] + subs
        args += self.chapters.write()
        args += self.metadata.write(_version(self.opts))
        if self.opts.webm:
            args += ['--webm']
        args += ['-o', self.source.final_file]
        _cmd(args)
    
    def clean_tmp(self):
        'Removes any temporary files generated during encoding.'
        Transcoder.clean_tmp(self)
        self.subtitles.clean_tmp()
        self.chapters.clean_tmp()
        self.metadata.clean_tmp()

class NullTranscoder(Transcoder):
    '''Does not actually perform any transcoding operations. Used to tag
    MPEG-4 video files which have already been transcoded.'''
    
    def __init__(self, source, opts):
        self.source = source
        self.opts = opts
        self._join = ''
        self._demux = ''
        self._wav = ''
        self.video = ''
        self.audio = ''
        self.subtitles = None
        self.chapters = None
        self.metadata = MP4Metadata(source)
        self.check()
    
    def check(self):
        'Checks if metadata tagging tools are installed.'
        if not self.metadata.enabled:
            raise RuntimeError('AtomicParsley is not installed.')
    
    def split(self):
        pass
    
    def join(self):
        pass
    
    def demux(self):
        pass
    
    def encode_video(self):
        pass
    
    def encode_audio(self):
        pass
    
    def remux(self):
        'Embeds metadata using AtomicParsley.'
        self.metadata.write(_version(self.opts))
    
    def clean_tmp(self):
        'Removes any temporary files generated during encoding.'
        self.metadata.clean_tmp()

class Source(dict):
    '''Acts as a base class for various raw video sources and handles
    Tvdb metadata.'''
    api_key = 'df4ac82a200af402cd0b7f44cac82a51'
    fps = None
    resolution = None
    duration = None
    surround = False
    cutlist = None
    vstreams = 0
    astreams = 0
    base = None
    orig = None
    rating = None
    final = None
    final_file = None
    meta_present = False
    split_args = None
    job = None
    
    def __repr__(self):
        season = int(self.get('season', 0))
        episode = int(self.get('episode', 0))
        prodcode = self.get('syndicatedepisodenumber', '(?)')
        show = self.get('title')
        name = self.get('subtitle')
        movie = self.get('movie')
        airdate = self.get('originalairdate')
        s = ''
        if movie and show:
            if airdate:
                s = u'%s (%d)' % (show, airdate.year)
            else:
                s = show
        elif show and name:
            if season > 0 and episode > 0:
                s = u'%s %02dx%02d - %s' % (show, season, episode, name)
            else:
                s = u'%s %s - %s' % (show, prodcode, name)
        else:
            s = self.base
        return u'<Source \'%s\' at %s>' % (s, hex(id(self)))
    
    def __init__(self, opts, defaults):
        self.opts = opts
        self.defaults = defaults
        if opts.tmp:
            self.remove_tmp = False
        else:
            opts.tmp = tempfile.mkdtemp(prefix = u'transcode_')
            self.remove_tmp = True
        if opts.container == 'mp4':
            if opts.ipod:
                self.ext = 'm4v'
            else:
                self.ext = 'mp4'
        if opts.container == 'mkv':
            if opts.webm:
                self.ext = 'webm'
            else:
                self.ext = 'mkv'
        self.tvdb = MythTV.ttvdb.tvdb_api.Tvdb(language = self.opts.language)
        ln = _iso_639_2(self.opts.language)
        cn = self.opts.country
        if cn is not None:
            cn = cn.upper()
        cache = os.path.join(tempfile.gettempdir(), 'tmdb3.cache')
        tmdb3.set_cache(engine = 'null')
        tmdb3.set_key(self.api_key)
        tmdb3.set_locale(language = ln, country = cn, fallthrough = 'en')
    
    def _check_split_args(self):
        '''Determines the arguments to pass to FFmpeg when copying video data
        during splits or frame queries. Versions 0.7 and older use -newaudio /
        -newvideo tags for each additional stream present. Versions 0.8 and
        newer use -map 0:v -map 0:a to automatically copy over all streams.'''
        has_c = _ver(['ffmpeg', '-help'], '^(-c codec)')
        if not has_c:
            args = [['-acodec', 'copy', '-vcodec', 'copy',
                     '-f', 'mpegts']]
            for astream in xrange(1, self.astreams):
                args += [['-acodec', 'copy', '-newaudio']]
            for vstream in xrange(1, self.vstreams):
                args += [['-vcodec', 'copy', '-newvideo']]
        else:
            args = [['-map', '0:v', '-map', '0:a', '-c', 'copy',
                     '-f', 'mpegts']]
        self.split_args = args
    
    def video_params(self):
        '''Obtains source media parameters such as resolution and FPS
        using ffmpeg.'''
        (fps, resolution, duration) = (None, None, None)
        (vstreams, astreams) = (0, 0)
        stream = 'Stream.*\[0x[0-9a-fA-F]+\].*'
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
                    vstreams += 1
                    if resolution is None:
                        width = int(match.group(1))
                        height = int(match.group(2))
                        resolution = (width, height)
                match = re.search(audioRE, line)
                if match:
                    astreams += 1
                match = re.search(duraRE, line)
                if match:
                    hour = int(match.group(1))
                    minute = int(match.group(2))
                    sec = int(match.group(3))
                    frac = int(match.group(4))
                    duration = hour * 3600 + minute * 60 + sec
                    duration += frac / (10. ** len(match.group(4)))
            proc.wait()
        except OSError:
            raise RuntimeError('FFmpeg is not installed.')
        if vstreams == 0:
            raise RuntimeError('No video streams could be found.')
        if astreams == 0:
            raise RuntimeError('No audio streams could be found.')
        self._check_split_args()
        return fps, resolution, duration, vstreams, astreams
    
    def parse_resolution(self, res):
        '''Translates the user-specified target resolution string into a
        width/height tuple using predefined resolution names like '1080p',
        or aspect ratios like '4:3', and so on.'''
        if res:
            predefined = {'480p' : (640, 480), '480p60' : (720, 480),
                          '720p' : (1280, 720), '1080p' : (1920, 1080)}
            for key, val in predefined.iteritems():
                if res == key:
                    return val
            match = re.match('(\d+)x(\d+)', res)
            if match:
                return (int(match.group(1)), int(match.group(2)))
            match = re.match('(\d+):(\d+)', res)
            if match:
                aspect = float(match.group(1)) / float(match.group(2))
                h = self.resolution[1]
                w = int(round(h * aspect))
                return (w, h)
            if res == 'close' or res == 'closest':
                (w, h) = self.resolution
                aspect = w * 1.0 / h
                closest = (-1920, -1080)
                for val in predefined.itervalues():
                    test = math.sqrt((val[0] - w) ** 2 + (val[1] - h) ** 2)
                    curr = math.sqrt((closest[0] - w) ** 2 +
                                     (closest[1] - h) ** 2)
                    if test < curr:
                        closest = val
                return closest
            logging.warning('*** Invalid resolution - %s ***' % res)
        return None
    
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
        lg = math.log(self['episodecount']) / math.log(10)
        field = int(math.ceil(lg))
        if field < 2:
            field = 2
        return ('%0' + str(field) + 'd') % ep
    
    def _collapse_movie(self):
        '''If the source video is a movie, rather than a TV show,
        applies the options for the movie subgroup to global options.'''
        if self.get('movie') is True:
            for key, val in self.defaults['.movie'].iteritems():
                setattr(self.opts, key, val)
    
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
    
    def _fetch_tvdb(self):
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
                    if self.opts.use_db_descriptions:
                        if len(self['description']) < len(overview):
                            self['description'] = overview
                rating = ep.get('rating')
                if rating is not None:
                    self['popularity'] = int(float(rating) / 10 * 255)
                    if self.opts.use_db_rating:
                        if self.get('description') is not None:
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
    
    def _add_tmdb_credits(self, movie):
        'Adds any cast members listed by TMDb if not already known.'
        tags = {'Screenplay' : 'screenwriter', 'Producer' : 'producer',
                'Executive Producer' : 'executive_producer',
                'Writer' : 'writer', 'Author' : 'writer', 'Editor' : 'editor',
                'Director' : 'director'}
        self['credits'] = []
        for person in movie.cast:
            self['credits'].append((person.name, 'actor'))
        for person in movie.crew:
            if tags.has_key(person.job):
                self['credits'].append((person.name, tags[person.job]))
    
    def _fetch_movie(self):
        'Attempts to find the movie in TMDb.'
        title = re.sub('-', '\\-', self.get('title'))
        if type(title) is unicode:
            title = title.encode('utf_8')
        print title
        results = tmdb3.searchMovie(title)
        if len(results) == 0:
            return None
        airdate = self.get('originalairdate')
        if airdate is not None and airdate.year > 1900:
            for m in results:
                if m.releasedate == airdate:
                    return m
        return results[0]
    
    def _fetch_tmdb(self):
        'Obtains missing movie metadata through TMDb.'
        if not self.get('title'):
            return
        try:
            movie = self._fetch_movie()
            if movie is None:
                logging.warning('*** Unable to fetch TMDb listings '
                                'for movie ***')
                return
            airdate = self.get('originalairdate')
            if airdate is None or airdate.year < 1900:
                self['originalairdate'] = movie.releasedate
            overview = movie.overview
            if self.get('description') is None:
                self['description'] = overview
            elif overview is not None:
                if self.opts.use_db_descriptions:
                    if len(self['description']) < len(overview):
                        self['description'] = overview
            rating = movie.userrating
            if rating is not None:
                self['popularity'] = int(float(rating) / 10 * 255)
                if self.opts.use_db_rating:
                    if self.get('description') is not None:
                        self['description'] += ' (%s / 10)' % rating
            cn = self.opts.country
            if cn is None or not movie.releases.has_key(cn.upper()):
                cn = 'US'
            else:
                cn = cn.upper()
            if movie.releases.has_key(cn):
                certification = movie.releases[cn].certification
                rating = self.get('rating')
                if rating is None or rating[:1] == '*':
                    self['rating'] = certification
            if self.get('category') is None:
                genres = movie.genres
                if genres is not None and len(genres) > 0:
                    self['category'] = genres[0].name
            self['tagline'] = movie.tagline
            poster = movie.poster
            if poster is not None:
                poster = poster.geturl()
                ext = os.path.splitext(poster)[-1]
                art = self.base + ext
                try:
                    urllib.urlretrieve(poster, art)
                    self['albumart'] = art
                except IOError:
                    logging.warning('*** Unable to download movie poster ***')
            self._add_tmdb_credits(movie)
        except tmdb3.tmdb_exceptions.TMDBError:
            logging.warning('*** Unable to fetch TMDb listings for movie ***')
    
    def fetch_database(self):
        'Obtains missing metadata from either Tvdb or TMDb.'
        if self.get('movie') == True:
            self._fetch_tmdb()
        else:
            self._fetch_tvdb()
    
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
    
    def print_options(self):
        'Outputs the user-selected options to the log.'
        logging.info('*** Printing configuration ***')
        fmt, audio, video = '', '', ''
        if self.opts.webm:
            fmt = 'WebM'
        elif self.opts.ipod:
            fmt = 'iPod Touch compatible MPEG-4'
        elif self.opts.container == 'mkv':
            fmt = 'Matroska'
        elif self.opts.container == 'mp4':
            fmt = 'MPEG-4'
        if self.opts.video == 'vp8':
            video = 'On2 VP8'
        elif self.opts.video == 'h264':
            video = 'H.264 AVC'
        if self.opts.audio == 'flac':
            audio = 'FLAC'
        elif self.opts.audio == 'vorbis':
            audio = 'Ogg Vorbis'
        elif self.opts.audio == 'aac':
            audio = 'AAC'
            if self.opts.aac_encoder == 'nero':
                audio += ' (neroAacEnc)'
            elif self.opts.aac_encoder == 'faac':
                audio += ' (libfaac)'
            elif self.opts.aac_encoder == 'ffmpeg-aac':
                audio += ' (ffmpeg-aac)'
        if type(self) != MP4Source:
            logging.info('  Format: %s, %s, %s' % (fmt, video, audio))
        enc = '  Video options:'
        if self.opts.preset:
            enc += ' preset \'%s\',' % self.opts.preset
        if self.opts.resolution:
            enc += ' resolution %dx%d,' % self.opts.resolution
        if self.opts.video == 'h264':
            if self.opts.h264_rc == 'crf':
                enc += ' crf = %d,' % self.opts.video_crf
            elif self.opts.h264_rc == 'cbr':
                enc += ' cbr = %d kb/s,' % self.opts.video_br
            if self.opts.h264_speed:
                enc += ' %s speed,' % self.opts.h264_speed
        if self.opts.video == 'vp8':
            if self.opts.vp8_rc == 'vbr':
                enc += ' vbr = %d kb/s,' % self.opts.video_br
            elif self.opts.vp8_rc == 'cbr':
                enc += ' cbr = %d kb/s,' % self.opts.video_br
            if self.opts.vp8_speed:
                enc += ' speed %s,' % self.opts.vp8_speed
        if self.opts.two_pass:
            enc += ' two-pass'
        else:
            enc += ' one-pass'
        if type(self) != MP4Source:
            logging.info(enc)
        logging.info('  Source file: %s' % self.orig)
        logging.info('  Target file: %s' % self.final_file)
        logging.info('  Temporary directory: %s' % self.opts.tmp)
    
    def final_name(self):
        '''Obtains the filename of the target MPEG-4 file using the format
        string. Formatting is (mostly) compatible with Recorded.formatPath()
        from dataheap.py, and the format used in mythrename.pl.'''
        final = os.path.join(self.opts.final_path, os.path.basename(self.base))
        if self.meta_present:
            path = re.sub('\\\\', '/', self.opts.format)
            tags = [('%T', 'title'), ('%S', 'subtitle'), ('%R', 'description'),
                    ('%C', 'category'), ('%n', 'syndicatedepisodenumber'),
                    ('%s', 'season'), ('%E', 'episode'), ('%r', 'rating')]
            for tag, key in tags:
                if self.get(key) is not None:
                    val = unicode(self.get(key))
                    val = val.replace(os.path.sep, self.opts.replace_char)
                    if os.path.altsep:
                        val = val.replace(os.path.altsep,
                                          self.opts.replace_char)
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
    db = None
    
    class _Rating(MythTV.DBDataRef):
        'Query for the content rating within the MythTV database.'
        _table = 'recordedrating'
        _ref = ['chanid', 'starttime']
    
    def __init__(self, jobid, opts, defaults):
        self._get_db(opts)
        try:
            self.job = MythTV.Job(jobid, db = self.db)
        except MythTV.exceptions.MythError:
            raise ValueError('Could not find job ID %d.' % jobid)
        channel = int(self.job.chanid)
        time = long(self.job.starttime.strftime('%Y%m%d%H%M%S'))
        self.__init__(channel, time, opts, defaults)
    
    def __init__(self, channel, time, opts, defaults):
        Source.__init__(self, opts, defaults)
        self.chanid = channel
        self.channel = channel
        self.time = _convert_time(time)
        self.base = os.path.join(opts.tmp, '%s_%s' % (str(channel), str(time)))
        self.orig = self.base + '-orig.mpg'
        self._get_db(opts)
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
        self.final_file = '%s.%s' % (self.final, self.ext)
    
    def _get_db(self, opts):
        'Connects to the MythTV MySQL database.'
        self.db_info = {'DBHostName' : opts.host, 'DBName' : opts.database,
                        'DBUserName' : opts.user, 'DBPassword' : opts.password,
                        'SecurityPin' : opts.pin}
        self.db = MythTV.MythDB(**self.db_info)
    
    def _frame_to_timecode(self, frame):
        '''Uses ffmpeg to remux a given number of frames in the video file
        in order to determine the amount of time elapsed by those frames.'''
        time = 0
        args = ['ffmpeg', '-y', '-i', self.orig, '-vframes',
                str(frame)] + self.split_args[0]
        args += [os.devnull]
        if len(self.split_args) > 1:
            args += self.split_args[1]
        proc = subprocess.Popen(args, stdout = subprocess.PIPE,
                                stderr = subprocess.STDOUT)
        logging.debug('$ %s' % u' '.join(args))
        regex = re.compile('time=(\d\d):(\d\d):(\d\d\.\d\d)(?!.*time)')
        for line in proc.stdout:
            match = re.search(regex, line)
            if match:
                time = 3600 * int(match.group(1)) + 60 * int(match.group(2))
                time += float(match.group(3))
        return time
    
    def _cut_list(self):
        'Obtains the MythTV commercial-skip cutlist from the database.'
        logging.info('*** Locating cut points ***')
        markup = self.rec.markup.getcutlist()
        self.cutlist = []
        for cut in xrange(0, len(markup)):
            start = self._frame_to_timecode(markup[cut][0])
            end = self._frame_to_timecode(markup[cut][1])
            self.cutlist.append((start, end))
    
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
        self._collapse_movie()
        self.fetch_database()
        self.sort_credits()
    
    def copy(self):
        '''Copies the recording for the given channel ID and start time to the
        specified path, if enough space is available.'''
        bs = 4096 * 1024
        logging.info('*** Copying video to %s ***' % self.orig)
        with self.rec.open() as source:
            with open(self.orig, 'wb') as dest:
                data = source.read(bs)
                while len(data) > 0:
                    dest.write(data)
                    data = source.read(bs)
        (self.fps, self.resolution, self.duration,
         self.vstreams, self.astreams) = self.video_params()
        if not self.fps or not self.resolution or not self.duration:
            raise RuntimeError('Could not determine video parameters.')
        self.opts.resolution = self.parse_resolution(self.opts.resolution)
        self._cut_list()
    
    def _clean_cutlist(self):
        '''Removes commercial-skip and cut marks from the cutlist.
        Adapted from http://www.mythtv.org/wiki/Transcode_wrapper_stub'''
        markup = []
        comm_start = self.rec.markup.MARK_COMM_START
        comm_end = self.rec.markup.MARK_COMM_END
        cut_start = self.rec.markup.MARK_CUT_START
        cut_end = self.rec.markup.MARK_CUT_END
        for (index, mark) in reversed(list(enumerate(self.rec.markup))):
            if mark.type in (comm_start, comm_end, cut_start, cut_end):
                del self.rec.markup[index]
        self.rec.markup.commit()
        self.rec.bookmark = 0
        self.rec.cutlist = 0
    
    def _rebuild_seek(self):
        'Queues a MythTV job to rebuild the seek table for the recording.'
        self.rec.seek.clean()
        data = {'chanid' : self.chanid, 'starttime' : self.time,
                'type' : MythTV.Job.COMMFLAG, 'args' : '--rebuild'}
        job = MythTV.Job(db = self.db).create(data = data)
    
    def import_mythtv(self):
        '''Imports the transcoded video into MythTV, overwriting the original
        MPEG-2 recording, and adjusting the Recorded table to match.'''
        bs = 4096 * 1024
        logging.info('*** Importing video into MythTV ***')
        self.rec.basename = os.path.basename(self.final_file)
        with open(self.final_file, 'r') as source:
            with self.rec.open('w') as dest:
                data = source.read(bs)
                while len(data) > 0:
                    dest.write(data)
                    data = source.read(bs)
        self._clean_cutlist()
        if self.opts.use_db_rating and self.get('popularity') is not None:
            self.rec.stars = round(self.get('popularity') / 51.0 * 2) / 10.0
        self.rec.filesize = long(os.path.getsize(self.final_file))
        self.rec.transcoded = 1
        self.rec.update()
        self._rebuild_seek()

    def import_mythvideo(self):
        '''Imports the transcoded video into MythTV's general-purpose video
        database (MythVideo) along with metadata.'''
        bs = 4096 * 1024
        logging.info('*** Importing video into MythVideo ***')
        
        
class WTVSource(Source):
    '''Obtains the raw MPEG-2 video data from a Windows TV recording (.WTV)
    along with embedded metadata.'''
    channel = None
    time = None
    orig = None
    
    def __init__(self, wtv, opts, defaults):
        Source.__init__(self, opts, defaults)
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
            f = os.path.basename(wtv)
            self.base = os.path.join(opts.tmp, os.path.splitext(f)[0])
        self.orig = self.base + '-orig.ts'
        self._fetch_metadata()
        self.final = self.final_name()
        self.final_file = '%s.%s' % (self.final, self.ext)
    
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
                        start = int(match.group(1)) / 29.97
                        end = int(match.group(2)) / 29.97
                        self.cutlist.append((start, end))
    
    def _parse_genre(self, genre):
        'Translates the WTV genre line into a category tag.'
        self['category'] = genre.split(';')[0]
    
    def _parse_airdate(self, airdate):
        'Translates the UTC timecode for original airdate into a date object.'
        try:
            d = datetime.datetime.strptime(airdate, '%Y-%m-%dT%H:%M:%SZ')
            if d.year >= 1900:
                self['originalairdate'] = d.date()
        except ValueError:
            pass
    
    def _parse_credits(self, line):
        'Translates the WTV credits line into a list of credited people.'
        cred = None
        people = line.split(';')
        if len(people) != 4:
            self['credits'] = []
            return
        for tup in zip(range(0, 4), ['actor', 'director',
                                     'host', 'guest_star']):
            for person in people[tup[0]].split('/'):
                if person != '':
                    if cred is None:
                        cred = []
                    cred.append((person, tup[1]))
        self['credits'] = cred
    
    def _parse_movie(self, line):
        '''Determines whether or not the WTV recording is of a feature-length
        movie.'''
        self['movie'] = (line.lower() == 'true')
    
    def _fetch_metadata(self):
        'Obtains any metadata which might be embedded in the WTV.'
        logging.info('*** Fetching metadata for %s ***' % self.wtv)
        val = '\s*:\s*(.*)$'
        tags = []
        tags.append((re.compile('service_provider' + val), 'channel'))
        tags.append((re.compile('service_name' + val), 'channel'))
        tags.append((re.compile('\s+Title' + val), 'title'))
        tags.append((re.compile('WM/SubTitle' + val), 'subtitle'))
        tags.append((re.compile('WM/SubTitleDescription' + val),
                     'description'))
        tags.append((re.compile('genre' + val), self._parse_genre))
        tags.append((re.compile('WM/MediaOriginalBroadcastDateTime' + val),
                     self._parse_airdate))
        tags.append((re.compile('WM/ParentalRating' + val), 'rating'))
        tags.append((re.compile('WM/MediaCredits' + val), self._parse_credits))
        tags.append((re.compile('WM/MediaIsMovie' + val), self._parse_movie))
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
        self._collapse_movie()
        self.fetch_database()
        self.sort_credits()
    
    def copy(self):
        'Extracts the MPEG-2 data from the WTV file.'
        logging.info('*** Extracting data to %s ***' % self.orig)
        try:
            _cmd(['java', '-cp', self.opts.remuxtool, 'util.WtvToMpeg',
                  '-i', self.wtv, '-o', self.orig, '-lang',
                  _iso_639_2(self.opts.language)])
        except RuntimeError:
            raise RuntimeError('Could not extract video.')
        (self.fps, self.resolution, self.duration,
         self.vstreams, self.astreams) = self.video_params()
        if not self.fps or not self.resolution or not self.duration:
            raise RuntimeError('Could not determine video parameters.')
        self.opts.resolution = self.parse_resolution(self.opts.resolution)
        self._cut_list()

class MP4Source(Source):
    '''Fetches Tvdb / TMDb metadata for an existing MPEG-4 or Matroska
    video file.'''
    channel = None
    
    def __init__(self, mp4, opts, defaults):
        Source.__init__(self, opts, defaults)
        if not os.path.exists(mp4):
            raise ValueError('Could not find file %s.' % mp4)
        self.ext = os.path.splitext(mp4)[-1]
        if self.ext[0] == '.':
            self.ext = self.ext[1:]
        b = os.path.basename(os.path.splitext(mp4)[0])
        self.base = os.path.join(opts.tmp, b)
        self.time = datetime.datetime.fromtimestamp(os.stat(mp4).st_ctime)
        self.orig = os.path.abspath(mp4)
        self.final = os.path.splitext(self.orig)[0]
        self.final_file = self.orig
        self._fetch_metadata()
    
    def _check(self, test, title, thresh = 0):
        'Determines whether a test string matches closely with the title.'
        if thresh == 0:
            thresh = max(int(round(len(title) * 0.25)), 3)
        test = test.lower()
        title = title.lower()
        if len(title) > 8 and test.find(title) >= 0:
            return True
        if _levenshtein(title, test) < thresh:
            return True
        return False
    
    def _check_movie(self, title, thresh = 0):
        '''Determines if a given title matches closely with the name of a
        movie in the TMDb database, within a given Levenshtein threshold.'''
        title = re.sub('-', '\\-', title)
        try:
            if re.search('\((\d\d\d\d)\)', title):
                movies = tmdb3.searchMovieWithYear(title)
                title = re.sub('\(\d\d\d\d\)', '', title).strip()
            else:
                movies = tmdb3.searchMovie(title)
        except tmdb3.tmdb_exceptions.TMDBError:
            return None
        for m in movies:
            t = m.title
            if self._check(t, title, thresh):
                return t, m
        return None
    
    def _check_show(self, title, thresh = 0):
        '''Determines if a given title matches closely with the name of a
        TV show in the Tvdb database, within a given Levenshtein threshold.'''
        try:
            show = self.tvdb[title].data.get('seriesname')
        except MythTV.ttvdb.tvdb_exceptions.tvdb_shownotfound:
            return None
        if self._check(show, title, thresh):
            return show
        return None
    
    def _check_episode(self, show, title, thresh = 0):
        '''Determines if a given title matches closely with the name of an
        episode of a TV show in the Tvdb database, within a given
        Levenshtein threshold.'''
        try:
            show = self.tvdb[show]
        except MythTV.ttvdb.tvdb_exceptions.tvdb_shownotfound:
            return None
        eps = show.search(title, key = 'episodename')
        for ep in eps:
            name = ep['episodename']
            if self._check(name, title):
                return name
        return None
    
    def _fetch_metadata(self):
        'Searches for the filename on Tvdb / TMDb.'
        path, title = os.path.split(os.path.splitext(self.orig)[0])
        path, first_dir = os.path.split(path)
        path, second_dir = os.path.split(path)
        titles = [x.strip() for x in title.split('-')]
        titles += [first_dir, second_dir]
        movie = self._check_movie(title)
        if movie is not None:
            self.meta_present = True
            self['movie'] = True
            self['title'] = movie[0]
            self['originalairdate'] = movie[1].releasedate
        else:
            for t in titles:
                show = self._check_show(t)
                if show is not None:
                    self.meta_present = True
                    self['movie'] = False
                    self['title'] = show
                    break
            if not self.meta_present:
                raise ValueError('Could not find match for %s.' % title)
            titles += title
            for t in titles:
                ep = self._check_episode(show, t)
                if ep is not None:
                    self['subtitle'] = ep
                    break
            if self.get('subtitle') is None:
                raise ValueError('Could not find episode for %s.' % title)
        self._collapse_movie()
        self.fetch_database()
        self.sort_credits()
    
    def copy(self):
        'Sets all video parameters to null, as they are not necessary.'
        self.fps = 0
        self.resolution = (0, 0)
        self.duration = 0
        self.vstreams = 0
        self.astreams = 0
        self.opts.resolution = self.resolution
    
    def clean_copy(self):
        pass

if __name__ == '__main__':
    defaults = _read_options()
    parser = _get_options(defaults)
    opts, args = parser.parse_args()
    _collapse_args(defaults, opts)
    _check_args(args, parser, opts)
    s = None
    if len(args) == 1:
        if args[0].isdigit():
            jobid = int(args[0])
            s = MythSource(jobid, opts, defaults)
        elif re.search('\.[Ww][Tt][Vv]', args[0]) is not None:
            wtv = args[0]
            s = WTVSource(wtv, opts, defaults)
        else:
            s = MP4Source(args[0], opts, defaults)
    else:
        channel = int(args[0])
        timecode = long(args[1])
        s = MythSource(channel, timecode, opts, defaults)
    s.copy()
    s.print_metadata()
    s.print_options()
    if type(s) == MP4Source:
        t = NullTranscoder(s, opts)
    elif opts.container == 'mkv':
        t = MKVTranscoder(s, opts)
    else:
        t = MP4Transcoder(s, opts)
    t.split()
    t.join()
    t.demux()
    s.clean_copy()
    t.encode_audio()
    t.clean_audio()
    t.encode_video()
    t.clean_video()
    t.remux()
    t.clean_tmp()
    s.clean_tmp()
    if type(s) == MythSource and opts.import_mythtv:
        s.import_mythtv()

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
