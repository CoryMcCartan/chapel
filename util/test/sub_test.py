#!/usr/bin/env python
#
# Rewrite of sub_test by Sung-Eun Choi (sungeun@cray.com)
#  sub_test is used by start_test in the Chapel Testing system
#  August 2009
#
# This script can be overridden with a script by the same name
#  placed in the test directory.
#
# The use and behavior of the various environment variables,
#  settings, and files were copied straight from sub_test.  They
#  were added/modified to sub_test over the years, and their use
#  is inconsistent and a bit of a mess.  I like to think that this
#  is due to the fact that the original sub_test was written in csh,
#  which was probably pretty novel at the time but is quite limited
#  by today's standards.  In addition, I implemented the timeout
#  mechanism directly rather than calling out to the timedexec
#  (perl) script.
#
# For compatibility reasons, I have maintained the behavior of the
#  original sub_test.  Any new features (e.g., internal timeout
#  mechanism) or modified behaviors (e.g., multiple .compopts,
#  multiple .execopts, custom .good files) will not interfere with
#  the expected behavior of tests that do not use the features or
#  behaviors.
#
#
# ENVIRONMENT VARIABLES:
#
# CHPL_HOME: Grabbed from the environment or deduced based on the path to
#    the compiler.
# CHPL_TEST_VGRND_COMP: Use valgrind on the compiler
# CHPL_TEST_VBRND_EXE: Use valgrind on the test program
# CHPL_VALGRIND_OPTS: Options to valgrind
# CHPL_TEST_FUTURES: 2 == test futures only
#                    1 == test futures and non-futures
#                    0 == test non-futures only
# CHPL_TEST_NOTESTS: Test the tests that are marked "notest" (see below)
# LAUNCHCMD: Uses this command to launch the test program
# CHPL_TEST_INTERP: DEPRECATED
# CHPL_TEST_PERF: Run as a performance test (same as -performance flag)
# CHPL_TEST_PERF_LABEL: The performance label, e.g. "perf"
# CHPL_TEST_PERF_DIR: Scratch directory for performance data
# CHPL_TEST_PERF_TRIALS: Default number of trials for perf tests
# CHPL_ONETEST: Name of the one test in this directory to run
# CHPL_TEST_SINGLES: If false, test the entire directory
# CHPL_SYSTEM_PREEXEC: If set, run script on test output prior to execution
# CHPL_SYSTEM_PREDIFF: If set, run that script on each test output
# CHPL_COMM: Chapel communication layer
# CHPL_COMPONLY: Only build the test (same as -noexec flag)
# CHPL_NO_STDIN_REDIRECT: do not redirect stdin when running tests
#                         also, skip tests with .stdin files
# CHPL_LAUNCHER_TIMEOUT: if defined, pass an option/options to the executable
#                        for it to enforce timeout instead of using timedexec;
#                        the value of the variable determines the option format.
# CHPL_TEST_TIMEOUT: The default global timeout to use.
# CHPL_TEST_UNIQUIFY_EXE: Uniquify the name of the test executable in the test
#                         system. CAUTION: This wont necessarily work for all
#                         tests, but can allow for running multiple start_tests
#                         over a directory in parallel.
# CHPL_TEST_ROOT_DIR: Absolute path to the test/ dir. Useful when test dir is
#                     not under $CHPL_HOME. Should not be set when test/ is
#                     under $CHPL_HOME. When it is set and the path prefixes a
#                     test in the logs, it will be removed (from the logs).
#
#
# DIRECTORY-WIDE FILES:  These settings are for the entire directory and
#  in many cases can be overridden or augmented with test-specific settings.
#
# NOEXEC: Do not execute tests in this directory
# NOVGRBIN: Do not execute valgrind
# COMPSTDIN: Get stdin from this file (default /dev/null)
# COMPOPTS: Compiler flags
# LASTCOMPOPTS: Compiler flags to be put at the end of the command line
# CHPLDOCOPTS: chpldoc flags
# EXECENV: Environment variables to be applied to the entire directory
# EXECOPTS: Test program flags to be applied to the entire directory
# LASTEXECOPTS: Test program flags to be put at the end of the command line
# NUMLOCALES: Number of locales to use
# CATFILES: List of files whose contents are added to end of test output
# PREDIFF: Script to execute before diff'ing output (arguments: <test
#    executable>, <log>, <compiler executable>)
# PREEXEC: Script to execute before executing test program (arguments: <test
#    executable>, <log>, <compiler executable>)
# PRECOMP: Script to execute before running the compiler (arguments: <test
#    executable>, <log>, <compiler executable>).
# PERFNUMTRIALS: Number of trials to run for performance testing
#
#
# TEST-SPECIFIC FILES:  These setting override or augment the directory-wide
#  settings.  Unless otherwise specified, these files are named
#  <test executable>.suffix (where suffix is one of the following).
#
# .good: "Golden" output file (can have different basenames)
# .compopts: Additional compiler options
# .perfcompopts: Additional compiler options for performance testing
# .lastcompopts: Additional compiler options to be added at the end of the
#    command line
# .chpldocopts: Additional chpldoc options.
# .execenv: Additional environment variables for the test
# .execopts: Additional test options
# .perfexecenv: Additional environment variables for performance testing
# .perfexecopts: Additional test options for performance testing
# .perfnumtrials: Number of trials to run for performance testing
# .notest: Do not run this test
# .numlocales: Number of locales to use (overrides NUMLOCALES)
# .future: Future test
# .ifuture: Future test
# .noexec: Do not execute this test
# .skipif: Skip this test if certain environment conditions hold true
# .suppressif: Suppress this test if certain environment conditions hold true
# .timeout: Test timeout (overrides TIMEOUT)
# .perftimeout: Performance test timeout
# .killtimeout: Kill timeout (overrides KILLTIMEOUT)
# .catfiles: Additional list of files whose contents are added to end of
#    test output
# .precomp: Additional script to execute before compiling the test
# .prediff: Additional script to execute before diff'ing output
# .preexec: Additional script to execute before executing test program
# .perfkeys: Existence indicates a performance test.  Contents specifies
#    performance "keys"
#
# In general, the performance label from CHPL_TEST_PERF_LABEL is used
# instead of "perf" in the above suffixes, and its all-caps version is used
# in the all-caps file names instead "PERF".

from __future__ import with_statement

import sys, os, subprocess, string, signal
import operator
import select, fcntl
import fnmatch, time
import re
import shlex
import datetime
import atexit
import logging


RUNNING = False

def run(_compiler, _args, _platform, _logger):
    global RUNNING # to suppress atexit handler 
    RUNNING = True

    global compiler, st_args, platform
    st_args = _args
    compiler = _compiler
    platform = _platform

    global logger
    logger = _logger

    global localdir, sub_test_start_time
    localdir = ''
    sub_test_start_time = time.time()
    
    get_settings()
    get_directory_options()
    valgrind_setup()
    setup()

    global directory_compopts, env_compopts, chpldoctopts, globalNumTrials
    global globalExecenv, globalExecopts, envExecopts, globalPrecomp
    global globalPrediff, globalPreexec, systemPrediff, systemPreexec

    (directory_compopts, env_compopts) = get_compopts()
    chpldocopts = get_chpldocopts()
    (globalNumTrials, globalExecenv, globalExecopts, envExecopts) = get_execopts()
    (globalPrecomp, globalPrediff, globalPreexec, sytstemPrediff, 
            systemPreexec) = pre_files()

    start_tests()
    
    return 0


def get_settings():
    if not os.access(compiler,os.R_OK|os.X_OK):
        Fatal('Cannot execute compiler \''+compiler+'\'')

    global is_chpldoc, is_chpl_ipe
    is_chpldoc = compiler.endswith('chpldoc')
    is_chpl_ipe = compiler.endswith('chpl-ipe')

    global path_to_compiler, chpl_base, tmp
    path_to_compiler = os.path.abspath(os.path.dirname(compiler))
    # Assume chpl binary is 2 directory levels down in the base installation
    (chpl_base, tmp) = os.path.split(path_to_compiler)
    (chpl_base, tmp) = os.path.split(chpl_base)
    chpl_base = os.path.normpath(chpl_base)

    # If $CHPL_HOME is not set, use the base installation of the compiler
    global chpl_home
    chpl_home = os.getenv('CHPL_HOME', chpl_base)
    chpl_home = os.path.normpath(chpl_home)

    # Find the test util directory -- set this in start_test to permit
    # a version of start_test other than the one in CHPL_HOME to be used
    global utildir
    utildir = os.getenv('CHPL_TEST_UTIL_DIR');
    if utildir is None or not os.path.isdir(utildir):
        Fatal('Cannot find test util directory {0}'.format(utildir))

    # Needed for MacOS mount points
    utildir = os.path.realpath(utildir)

    # Find the c compiler
    # We open the compileline inside of CHPL_HOME rather than CHPL_TEST_UTIL_DIR on
    # purpose. compileline will not work correctly in some configurations when run
    # outside of its directory tree.
    global c_compiler
    p = subprocess.Popen([os.path.join(chpl_home,'util','config','compileline'),
                            '--compile'],
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    c_compiler = p.communicate()[0].rstrip()
    if p.returncode != 0:
      Fatal('Cannot find c compiler')

    # Find the test directory
    global testdir
    testdir = chpl_home+'/test'
    if os.path.isdir(testdir) == 0:
        testdir = chpl_home+'/examples'
        if os.path.isdir(testdir) == 0:
            Fatal('Cannot find test directory '+chpl_home+'/test or '+testdir)
    # Needed for MacOS mount points
    testdir = os.path.realpath(testdir)

    # If user specified a different test directory (e.g. with --test-root flag on
    # start_test), use it instead.
    global test_root_dir
    test_root_dir = st_args.test_root_dir 
    if test_root_dir is not None:
        testdir = test_root_dir

    # Use timedexec
    # As much as I hate calling out to another script for the time out stuff,
    #  subprocess doesn't quite cut it for this kind of stuff
    global useTimedExec, timedexec
    useTimedExec = True
    if useTimedExec:
        timedexec = utildir+'/test/timedexec'
        if not os.access(timedexec,os.R_OK|os.X_OK):
            Fatal('Cannot execute timedexec script \''+timedexec+'\'')

    # Machine name we are running on
    global machine
    machine = os.uname()[1].split('.', 1)[0]

    global useLauncherTimeout
    # Use the launcher walltime option for timeout
    useLauncherTimeout = st_args.launcher_timeout

    global uniquifyTests
    uniquifyTests = False
    if os.getenv('CHPL_TEST_UNIQUIFY_EXE') != None:
        uniquifyTests = True

    global localdir
    # Get the current directory (normalize for MacOS case-sort-of-sensitivity)
    localdir = string.replace(os.path.normpath(os.getcwd()), testdir, '.')

    if localdir.find('./') == 0:
        # strip off the leading './'
        localdir = string.lstrip(localdir, '.')
        localdir = string.lstrip(localdir, '/')
    
    global chplcomm, chplcommstr, chpllauncher, chpllm, chpllmstr
    # CHPL_COMM
    chplcomm=os.getenv('CHPL_COMM','none').strip()
    chplcommstr='.comm-'+chplcomm

    # CHPL_LAUNCHER
    chpllauncher=os.getenv('CHPL_LAUNCHER','none').strip()

    # CHPL_LOCALE_MODEL
    chpllm=os.getenv('CHPL_LOCALE_MODEL','flat').strip()
    chpllmstr='.lm-'+chpllm


def get_directory_options():
    global perftest, perflabel, perfdir, perfdescription
    if st_args.performance:
        perftest = True
        perflabel = st_args.perflabel 
        perfdir = os.getenv('CHPL_TEST_PERF_DIR')
        perfdescription = st_args.performance_description
        if perfdescription != "" and perfdescription != "default":
            logger.write('Setting perfdir to %s from %s because of additional perf description' %(os.path.join(perfdir, perfdescription), perfdir))
            perfdir = os.path.join(perfdir, perfdescription)
        else:
            perfdescription= ''
        if perflabel == None or perfdir == None:
            Fatal('$CHPL_TEST_PERF_DIR and $CHPL_TEST_PERF_LABEL must be set for performance testing')
    else:
        perftest=False
        perflabel=''

    global compoptssuffix, chpldocsuffix, execenvsuffix, execoptssuffix
    global timeoutsuffix
    compoptssuffix = PerfSfx('compopts')  # .compopts or .perfcompopts or ...

    # If compiler is chpldoc, use .chpldocopts for options.
    chpldocsuffix = '.chpldocopts'

    execenvsuffix  = PerfSfx('execenv')   # .execenv  or .perfexecenv  or ...
    execoptssuffix = PerfSfx('execopts')  # .execopts or .perfexecopts or ...
    timeoutsuffix  = PerfSfx('timeout')   # .timeout  or .perftimeout  or ...

    # Get global timeout
    global globalTimeout
    if st_args.valgrind:
        globalTimeout=1000
    else:
        globalTimeout=300
    globalTimeout = int(os.getenv('CHPL_TEST_TIMEOUT', globalTimeout))

    # get a threshold fo which to report long running tests
    global execTimeWarnLimit
    if os.getenv("CHPL_TEST_EXEC_TIME_WARN_LIMIT"):
        execTimeWarnLimit = int(os.getenv('CHPL_TEST_EXEC_TIME_WARN_LIMIT', '0'))
    else:
        execTimeWarnLimit = 0

    # directory level timeout
    global directoryTimeout
    if os.access('./TIMEOUT',os.R_OK):
        directoryTimeout = ReadIntegerValue('./TIMEOUT', localdir)
    else:
        directoryTimeout = globalTimeout

    # Check for global PERFTIMEEXEC option
    global timerFile, globalTimer
    timerFile = PerfDirFile('TIMEEXEC') # e.g. ./PERFTIMEEXEC
    if os.access(timerFile, os.R_OK):
        globalTimer = GetTimer(timerFile)
    else:
        globalTimer = None

    # Get global timeout for kill
    global globalKillTimeout
    if os.access('./KILLTIMEOUT',os.R_OK):
        globalKillTimeout = ReadIntegerValue('./KILLTIMEOUT', localdir)
    else:
        globalKillTimeout=10

    global execute, vgrbin, compstdin

    if os.access('./NOEXEC',os.R_OK):
        execute=False
    else:
        execute=True

    if os.access('./NOVGRBIN',os.R_OK):
        vgrbin=False
    else:
        vgrbin=True

    if os.access('./COMPSTDIN',os.R_OK):
        compstdin='./COMPSTDIN'
    else:
        compstdin='/dev/null'

    global globalLastcompopts, globalLastexecopts, globalNumlocales

    globalLastcompopts=list();
    if os.access('./LASTCOMPOPTS',os.R_OK):
        globalLastcompopts+=subprocess.Popen(['cat', './LASTCOMPOPTS'], stdout=subprocess.PIPE).communicate()[0].strip().split()

    globalLastexecopts=list();
    if os.access('./LASTEXECOPTS',os.R_OK):
        globalLastexecopts+=subprocess.Popen(['cat', './LASTEXECOPTS'], stdout=subprocess.PIPE).communicate()[0].strip().split()

    if os.access(PerfDirFile('NUMLOCALES'),os.R_OK):
        globalNumlocales=ReadIntegerValue(PerfDirFile('NUMLOCALES'), localdir)
        # globalNumlocales.strip(globalNumlocales)
    else:
        # start_test sets this, so we'll assume it's right :)
        globalNumlocales = st_args.num_locales

    global globalCatfiles

    if os.access('./CATFILES',os.R_OK):
        globalCatfiles=subprocess.Popen(['cat', './CATFILES'], stdout=subprocess.PIPE).communicate()[0]
        globalCatfiles.strip(globalCatfiles)
    else:
        globalCatfiles=None


def valgrind_setup():
    global chpl_valgrind_opts, valgrindcomp, valgrindcompopts, valgrindbin
    global valgrindbinopts

    chpl_valgrind_opts = os.getenv('CHPL_VALGRIND_OPTS', '--tool=memcheck')

    if st_args.valgrind:
        valgrindcomp = 'valgrind'
        valgrindcompopts = chpl_valgrind_opts.split()
        valgrindcompopts += ['--gen-suppressions=all']
        valgrindcompopts += ['--suppressions=%s/compiler/etc/valgrind.suppressions'%(chpl_home)]
        valgrindcompopts += ['-q']
    else:
        valgrindcomp = None
        valgrindcompopts = None

    if (st_args.valgrind_exe and vgrbin):
        valgrindbin = 'valgrind'
        valgrindbinopts = chpl_valgrind_opts.split()+['-q']
        if (chplcomm != 'none'):
            valgrindbinopts += ['--trace-children=yes']
    else:
        valgrindbin = None
        valgrindbinopts = None


def setup():
    global testfutures, testnotests, launchcmd, futureSuffix, printpassesfile
    global compperftest, compperfdir, keyfile, tempDatFilesDir

    testfutures=string.atoi(os.getenv('CHPL_TEST_FUTURES','0'))

    testnotests=os.getenv('CHPL_TEST_NOTESTS')

    launchcmd = st_args.launch_cmd

    futureSuffix='.future'

    printpassesfile = None
    if st_args.comp_performance:
        compperftest=True
        
        # check for the main compiler performance directory
        if os.getenv('CHPL_TEST_COMP_PERF_DIR')!=None:
            compperfdir=os.getenv('CHPL_TEST_COMP_PERF_DIR')
        else:
            compperfdir=chpl_home+'/test/compperfdat/' 
        
        # The env var CHPL_PRINT_PASSES_FILE will cause the 
        # compiler to save the pass timings to specified file.
        if os.getenv('CHPL_PRINT_PASSES_FILE')!=None:
            printpassesfile=os.getenv('CHPL_PRINT_PASSES_FILE')
        else:
            printpassesfile='timing.txt'
            os.putenv('CHPL_PRINT_PASSES_FILE', 'timing.txt')
          
        # check for the perfkeys file
        if os.getenv('CHPL_TEST_COMP_PERF_KEYS')!=None:
            keyfile=os.getenv('CHPL_TEST_COMP_PERF_KEYS')
        else: 
            keyfile=chpl_home+'/test/performance/compiler/compilerPerformance.perfkeys'
            
        # Check for the directory to store the tempory .dat files that will get 
        # combined into one.    
        if os.getenv('CHPL_TEST_COMP_PERF_TEMP_DAT_DIR')!=None:
            tempDatFilesDir = os.getenv('CHPL_TEST_COMP_PERF_TEMP_DAT_DIR')
        else: 
            tempDatFilesDir = compperfdir + 'tempCompPerfDatFiles/'
            
    else: 
        compperftest=False

#
# Global COMPOPTS/PERFCOMPOPTS:
#
#   Prefer PERFCOMPOPTS if doing performance testing; otherwise, use
#   COMPOPTS.  Note that COMPOPTS is used for performance testing
#   currently in the absence of a PERFCOMPOPTS file.  Not sure whether
#   or not this is a good idea, but preserving it for now for backwards
#   compatibility.
#
def get_compopts():
    directoryCompopts = list(' ')
    if (perftest and os.access(PerfDirFile('COMPOPTS'),os.R_OK)): # ./PERFCOMPOPTS
        directoryCompopts=ReadFileWithComments(PerfDirFile('COMPOPTS'))
    elif os.access('./COMPOPTS',os.R_OK):
        directoryCompopts=ReadFileWithComments('./COMPOPTS')

    envCompopts = st_args.compopts
    if envCompopts is not None:
        envCompopts = shlex.split(envCompopts)
    else:
      envCompopts = []

    return (directoryCompopts, envCompopts)


def get_chpldocopts():
    # Global CHPLDOCOPTS
    if os.access('./CHPLDOCOPTS', os.R_OK):
        dirChpldocOpts = shlex.split(ReadFileWithComments('./CHPLDOCOPTS')[0])
    else:
        dirChpldocOpts = []

    # Env CHPLDOCOPTS
    envChpldocOpts = os.getenv('CHPLDOCOPTS')
    if envChpldocOpts is not None:
        envChpldocOpts = shlex.split(envChpldocOpts)
    else:
        envChpldocOpts = []

    # Global chpldoc options.
    return dirChpldocOpts + envChpldocOpts


# Global EXECOPTS/PERFEXECOPTS
#
#
#   Prefer PERFEXECOPTS if doing performance testing; otherwise, use
#   EXECOPTS.  Note that EXECOPTS is used for performance testing
#   currently in the absence of a PERFEXECOPTS file.  Not sure whether
#   or not this is a good idea, but preserving it for now for backwards
#   compatibility.
#
def get_execopts():
    if perftest and os.access(PerfDirFile('NUMTRIALS'), os.R_OK): # ./PERFNUMTRIALS
        globalNumTrials = ReadIntegerValue(PerfDirFile('NUMTRIALS'), localdir)
    else:
        globalNumTrials = int(st_args.num_trials)

    if os.access('./EXECENV',os.R_OK):
        globalExecenv = ReadFileWithComments('./EXECENV')
    else:
        globalExecenv = list()

    if (perftest and os.access(PerfDirFile('EXECOPTS'),os.R_OK)): # ./PERFEXECOPTS
        tgeo = ReadFileWithComments(PerfDirFile('EXECOPTS'))
        globalExecopts = shlex.split(tgeo[0])
    elif os.access('./EXECOPTS',os.R_OK):
        tgeo = ReadFileWithComments('./EXECOPTS')
        globalExecopts = shlex.split(tgeo[0])
    else:
        globalExecopts = list()

    envExecopts = st_args.execopts

    return (globalNumTrials, globalExecenv, globalExecopts, envExecopts)

#
# Global PRECOMP, PREDIFF & PREEXEC
#
def pre_files():
    global globalPrecomp, globalPrediff, globalPreexec, systemPreexec
    global systemPrediff

    if os.access('./PRECOMP', os.R_OK|os.X_OK):
        globalPrecomp='./PRECOMP'
    else:
        globalPrecomp=None
    #
    if os.access('./PREDIFF',os.R_OK|os.X_OK):
        globalPrediff='./PREDIFF'
    else:
        globalPrediff=None
    if os.access('./PREEXEC',os.R_OK|os.X_OK):
        globalPreexec='./PREEXEC'
    else:
        globalPreexec=None

    # Get the system-wide preexec
    systemPreexec = st_args.preexec
    if systemPreexec is not None:
        if not os.access(systemPreexec, os.R_OK|os.X_OK):
            Fatal("Cannot execute system-wide preexec '{0}'".format(systemPreexec))

    # Get the system-wide prediff
    systemPrediff = st_args.prediff
    if systemPrediff:
      if not os.access(systemPrediff,os.R_OK|os.X_OK):
        Fatal('Cannot execute system-wide prediff \''+systemPrediff+'\'')

    return (globalPrecomp, globalPrediff, globalPreexec, systemPrediff,
            systemPreexec)


def start_tests():
    logger.write('[Starting subtest - %s]'%(time.strftime('%a %b %d %H:%M:%S %Z %Y', time.localtime())))
    if systemPreexec:
        logger.write("[system-wide preexec: '{0}']".format(systemPreexec))
    if systemPrediff:
        logger.write('[system-wide prediff: \'%s\']'%(systemPrediff))

    # consistently look only at the files in the current directory
    dirlist=os.listdir(".")

    onetestsrc = os.getenv('CHPL_ONETEST')
    if onetestsrc == None:
        testsrc=filter(IsChplTest, dirlist)
    else:
        testsrc=list()
        testsrc.append(onetestsrc)

    global compiler
    original_compiler = compiler

    for testname in testsrc:
        logger.flush()

        compiler = original_compiler

        # print testname
        logger.write('[test: %s/%s]'%(localdir,testname))
        test_filename = re.match(r'^(.*)\.(?:chpl|test\.c)$', testname).group(1)
        execname = test_filename
        if uniquifyTests:
            execname += '.{0}'.format(os.getpid())
        # print test_filename

        if re.match(r'^.+\.test\.c$', testname):
          is_c_test = True
        else:
          is_c_test = False

        # If the test name ends with .doc.chpl or the compiler was set to chpldoc
        # (i.e. is_chpldoc=True), run this test with chpldoc options.
        if testname.endswith('.doc.chpl') or is_chpldoc:
            test_is_chpldoc = True
        else:
            test_is_chpldoc = False

        # Test specific settings
        catfiles = globalCatfiles
        numlocales = globalNumlocales
        lastcompopts = list()
        if globalLastcompopts:
            lastcompopts += globalLastcompopts
        lastexecopts = list()
        if globalLastexecopts:
            lastexecopts += globalLastexecopts

        # Get the list of files starting with 'test_filename.'
        test_filename_files = fnmatch.filter(dirlist, test_filename+'.*')
        # print test_filename_files, dirlist

        if (perftest and (test_filename_files.count(PerfTFile(test_filename,'keys'))==0) and
            (test_filename_files.count(PerfTFile(test_filename,'execopts'))==0)):
            logger.write('[Skipping noperf test: %s/%s]'%(localdir,test_filename))
            continue # on to next test

        timeout = directoryTimeout
        killtimeout = globalKillTimeout
        numTrials = globalNumTrials
        if (perftest):
            timer = globalTimer
        else:
            timer = None
        futuretest=''

        if test_is_chpldoc or is_chpl_ipe:
            executebin = False
        else:
            executebin = execute

        testfuturesfile=False
        testskipiffile=False
        noexecfile=False
        execoptsfile=False
        precomp=None
        prediff=None
        preexec=None

        if not st_args.no_stdin_redirect and not st_args.stdin_redirect:
            redirectin = '/dev/null'
        else:
            redirectin = None

        # If there is a .skipif file, put it at front of list.
        skipif_i = -1
        for i, test_filename_file in enumerate(test_filename_files):
            if test_filename_file.endswith('.skipif'):
                skipif_i = i
                break
        if skipif_i > 0:
            test_filename_files.insert(0, test_filename_files.pop(skipif_i))

        # Deal with these files
        do_not_test=False
        for f in test_filename_files:
            (root, suffix) = os.path.splitext(f)

            # 'f' is of the form test_filename.SOMETHING.suffix,
            # not pertinent at the moment
            if root != test_filename:
                continue

            # Deal with these later
            if (suffix == '.good' or
                suffix=='.compopts' or suffix=='.perfcompopts' or
                suffix=='.chpldocopts' or
                suffix=='.execenv' or suffix=='.perfexecenv' or
                suffix=='.execopts' or suffix=='.perfexecopts'):
                continue # on to next file

            elif (suffix=='.notest' and (os.access(f, os.R_OK) and
                                         testnotests=='0')):
                logger.write('[Skipping notest test: %s/%s]'%(localdir,test_filename))
                do_not_test=True
                break

            elif (suffix=='.skipif' and (os.access(f, os.R_OK) and
                   (os.getenv('CHPL_TEST_SINGLES')=='0'))):
                testskipiffile=True
                skiptest=runSkipIf(f)
                try:
                    skipme=False
                    if skiptest.strip() != "False":
                        skipme = skiptest.strip() == "True" or int(skiptest) == 1
                    if skipme:
                        logger.write('[Skipping test based on .skipif environment settings: %s/%s]'%(localdir,test_filename))
                        do_not_test=True
                except ValueError:
                    logger.write('[Error processing .skipif file %s/%s]'%(localdir,f))
                    do_not_test=True
                if do_not_test:
                    break

            elif (suffix=='.suppressif' and (os.access(f, os.R_OK))):
                suppresstest=runSkipIf(f)
                try:
                    suppressme=False
                    if suppresstest.strip() != "False":
                        suppressme = suppresstest.strip() == "True" or int(suppresstest) == 1
                    if suppressme:
                        suppressline = ""
                        with open('./'+test_filename+'.suppressif', 'r') as suppressfile:
                            for line in suppressfile:
                                line = line.strip()
                                if (line.startswith("#") and
                                    not line.startswith("#!")):
                                    suppressline = line.replace('#','').strip()
                                    break
                        futuretest='Suppress (' + suppressline + ') '
                except ValueError:
                    logger.write('[Error processing .suppressif file %s/%s]'%(localdir,f))

            elif (suffix == timeoutsuffix and os.access(f, os.R_OK)):
                timeout=ReadIntegerValue(f, localdir)
                logger.write('[Overriding default timeout with %d]'%(timeout))
            elif (perftest and suffix == PerfSfx('timeexec') and os.access(f, os.R_OK)): #e.g. .perftimeexec
                timer = GetTimer(f)

            elif (perftest and suffix == PerfSfx('numtrials') and os.access(f, os.R_OK)): #e.g. .perfnumtrials
                numTrials = ReadIntegerValue(f, localdir)

            elif (suffix=='.killtimeout' and os.access(f, os.R_OK)):
                killtimeout=ReadIntegerValue(f, localdir)

            elif (suffix=='.catfiles' and os.access(f, os.R_OK)):
                execcatfiles=subprocess.Popen(['cat', f], stdout=subprocess.PIPE).communicate()[0].strip()
                if catfiles:
                    catfiles+=execcatfiles
                else:
                    catfiles=execcatfiles

            elif (suffix=='.lastcompopts' and os.access(f, os.R_OK)):
                lastcompopts+=subprocess.Popen(['cat', f], stdout=subprocess.PIPE).communicate()[0].strip().split()

            elif (suffix=='.lastexecopts' and os.access(f, os.R_OK)):
                lastexecopts+=subprocess.Popen(['cat', f], stdout=subprocess.PIPE).communicate()[0].strip().split()

            elif (suffix == PerfSfx('numlocales') and os.access(f, os.R_OK)):
                numlocales=ReadIntegerValue(f, localdir)

            elif suffix == futureSuffix and os.access(f, os.R_OK):
                with open('./'+test_filename+futureSuffix, 'r') as futurefile:
                    futuretest='Future ('+futurefile.readline().strip()+') '

            elif (suffix=='.noexec' and os.access(f, os.R_OK)):
                noexecfile=True
                executebin=False

            elif (suffix=='.precomp' and os.access(f, os.R_OK|os.X_OK)):
                precomp=f

            elif (suffix=='.prediff' and os.access(f, os.R_OK|os.X_OK)):
                prediff=f

            elif (suffix=='.preexec' and os.access(f, os.R_OK|os.X_OK)):
                preexec=f

            elif (suffix=='.stdin' and os.access(f, os.R_OK)):
                if redirectin == None:
                    logger.write('[Skipping test with .stdin input since -nostdinredirect is given: %s/%s]'%(localdir,test_filename))
                    do_not_test=True
                    break
                else:
                    # chpl-ipe only has a "compile" step, so any stdin needs to be
                    # passed to compiler.
                    global compstdin
                    if is_chpl_ipe:
                        compstdin = f
                    else:
                        redirectin = f

            if suffix == futureSuffix:
                testfuturesfile=True

        del test_filename_files

        # Skip to the next test
        if do_not_test:
            continue # on to next test

        # 0: test no futures
        if testfutures == 0 and testfuturesfile == True:
            logger.write('[Skipping future test: %s/%s]'%(localdir,test_filename))
            continue # on to next test
        # 1: test all futures
        elif testfutures == 1:
            pass
        # 2: test only futures
        elif testfutures == 2 and testfuturesfile == False:
            logger.write('[Skipping non-future test: %s/%s]'%(localdir,test_filename))
            continue # on to next test
        # 3: test futures that have a .skipif file
        elif testfutures == 3 and testfuturesfile == True and testskipiffile == False:
            logger.write('[Skipping future test without a skipif: %s/%s]'%(localdir,test_filename))
            continue # on to next test

        # c tests don't have a way to launch themselves
        if is_c_test and chpllauncher != 'none':
            logger.write('[Skipping c test: %s/%s]'%(localdir,test_filename))
            continue

        # Set numlocales
        if (numlocales == 0) or (chplcomm=='none') or is_c_test:
            numlocexecopts = None
        else:
            numlocexecopts = ' -nl '+str(numlocales)

        # if any performance test has a timeout longer than the default we only
        # want to run it once
        if (timeout > globalTimeout):
            if numTrials != 1:
                logger.write('[Lowering number of trials for {0} to 1]'.format(test_filename))
                numTrials = 1

        # Get list of test specific compiler options
        # Default to [' ']
        compoptslist = list(' ')

        chpldoc_opts_filename = test_filename + chpldocsuffix
        if test_is_chpldoc and os.access(chpldoc_opts_filename, os.R_OK):
            compoptslist = ReadFileWithComments(chpldoc_opts_filename, False)
            if not compoptslist:
                logger.write('[Warning: ignoring an empty chpldocopts file %s]' %
                                 (test_filename+compoptssuffix))
        elif os.access(test_filename+compoptssuffix, os.R_OK):
            compoptslist = ReadFileWithComments(test_filename+compoptssuffix, False)
            if not compoptslist:
                # cf. for execoptslist no warning is issued
                logger.write('[Warning: ignoring an empty compopts file %s]'%(test_filename+compoptssuffix))

        # Merge global compopts list with local compopts.
        # Use the "product" of the two if they are both provided.
        usecompoptslist = [ ]
        # Note -- this could use itertools.product
        for dir_compopts in directory_compopts:
            for file_compopts in compoptslist:
                useopt = [dir_compopts, file_compopts]
                usearg = ' '.join(useopt)
                # But change all-spaces into single space.
                if usearg.strip() == '':
                  usearg = ' '
                usecompoptslist += [usearg]
        compoptslist = usecompoptslist

        # The test environment is that of this process, augmented as specified
        if os.access(test_filename+execenvsuffix, os.R_OK):
            execenv = ReadFileWithComments(test_filename+execenvsuffix)
        else:
            execenv = list()

        testenv = {}
        if len(globalExecenv)!=0 or len(execenv)!=0:
            for tev in globalExecenv:
                testenv[tev.split('=')[0].strip()] = tev.split('=')[1].strip()
            for tev in execenv:
                testenv[tev.split('=')[0].strip()] = tev.split('=')[1].strip()
            del tev

        # Get list of test specific exec options
        if os.access(test_filename+execoptssuffix, os.R_OK):
            execoptsfile=True
            execoptslist = ReadFileWithComments(test_filename+execoptssuffix, False)
        else:
            execoptslist = list()
        # Handle empty execopts list
        if len(execoptslist) == 0:
            # cf. for compoptslist, a warning is issued in this case
            execoptslist.append(' ')

        clist = list()
        curFileTestStart = time.time()

        # For all compopts + execopts combos..
        compoptsnum = 0
        for compopts in compoptslist:
            logger.flush()
            del clist
            # use the remaining portion as a .good file for executing tests
            #  clist will be *added* to execopts if it is empty, or just used
            #  as the default .good file if not empty
            clist = compopts.split('#')
            if len(clist) >= 2:
                compopts = clist.pop(0)
                cstr = ' #' + '#'.join(clist)
                del clist[:]
                clist.append(cstr)
            else:
                del clist[:]

            if compopts == ' ':
                complog=execname+'.comp.out.tmp'
            else:
                compoptsnum += 1
                complog = execname+'.'+str(compoptsnum)+'.comp.out.tmp'

            #
            # Run the precompile script
            #
            if globalPrecomp:
                logger.write('[Executing ./PRECOMP]')
                logger.flush()
                subprocess.Popen(['./PRECOMP',
                                 execname,complog,compiler]).wait()

            if precomp:
                logger.write('[Executing precomp %s.precomp]'%(test_filename))
                logger.flush()
                subprocess.Popen(['./'+test_filename+'.precomp',
                                 execname,complog,compiler]).wait()


            #
            # Build the test program
            #
            args = []
            if test_is_chpldoc:
                args += globalChpldocOpts + shlex.split(compopts)
            elif is_chpl_ipe:
                # No arguments work for chpl-ipe as of 2015-04-08. (thomasvandoren)
                # TODO: When chpl-ipe does support command line flags, decide if it
                #       will use COMPOPTS/.compopts or some other filename.
                #       (thomasvandoren, 2015-04-08)
                pass
            else:
                args += ['-o', execname] + env_compopts + shlex.split(compopts)
            args += [testname]

            if is_c_test:
                # we need to drop envCompopts for C tests as those are options
                # for `chpl` so don't include them here
                args = ['-o', test_filename]+shlex.split(compopts)+[testname]
                cmd = c_compiler
            else:
                if test_is_chpldoc and not compiler.endswith('chpldoc'):
                    # For tests with .doc.chpl suffix, use chpldoc compiler. Update
                    # the compopts accordingly. Add 'doc' prefix to existing compiler.
                    compiler += 'doc'
                    cmd = compiler

                    if which(cmd) is None:
                        logger.write(
                            '[Warning: Could not find chpldoc, skipping test '
                            '{0}/{1}]'.format(localdir, test_filename))
                        break

                if valgrindcomp:
                    cmd = valgrindcomp
                    args = valgrindcompopts+[compiler]+args
                else:
                    cmd = compiler

            if lastcompopts:
                args += lastcompopts

            compStart = time.time()
            #
            # Compile (with timeout)
            #
            # compilation timeout defaults to 2 * execution timeout.
            # This is to quiet compilation timeouts in some oversubscribed test
            # configurations (since they are generating a lot of testing noise, but
            # don't represent a real issue.)
            #
            # TODO (Elliot 02/27/15): Ideally what we want is separate options for
            # compiler and testing timeout, but that's more work to thread through
            # sub_test right now and this is causing a lot of noise in nightly
            # testing. Hopefully this is just a temporary work around and I'll
            # remember to add the cleaner solution soon.
            #
            comptimeout = 2*timeout
            cmd=ShellEscapeCommand(cmd);
            loggerout = '[Executing compiler %s'%(cmd)
            if args:
                loggerout += ' {}'.format(' '.join(args))
            logger.write('{} < {}]'.format(loggerout, compstdin))
            if useTimedExec:
                wholecmd = cmd+' '+' '.join(map(ShellEscape, args))
                p = subprocess.Popen([timedexec, str(comptimeout), wholecmd],
                                     stdin=open(compstdin, 'r'),
                                     stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT)
                output = p.communicate()[0]
                status = p.returncode

                if status == 222:
                    loggerout = ('{}[Error: Timed out compilation for {}/{}'
                            .format(futuretest, localdir, test_filename))
                    loggerout += printTestVariation(compoptsnum, compoptslist)
                    logger.write('{}]'.format(loggerout))
                    cleanup(execname)
                    cleanup(printpassesfile)
                    continue # on to next compopts

            else:
                p = subprocess.Popen([cmd]+args, stdin=open(cmpstdin, 'r'),
                                     stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT)
                try:
                    output = SuckOutputWithTimeout(p.stdout, comptimeout)
                except ReadTimeoutException:
                    loggerout = ('%s[Error: Timed out compilation for %s/%s'%
                                     (futuretest, localdir, test_filename))
                    loggerout += printTestVariation(compoptsnum, compoptslist);
                    logger.write('{}]'.format(loggerout))
                    KillProc(p, killtimeout)
                    cleanup(execname)
                    cleanup(printpassesfile)
                    continue # on to next compopts

                status = p.returncode

            elapsedCompTime = time.time() - compStart
            test_name = os.path.join(localdir, test_filename)
            if compoptsnum != 0:
                test_name += ' (compopts: {0})'.format(compoptsnum)

            logger.write('[Elapsed compilation time for "{0}" - {1:.3f} '
                'seconds]'.format(test_name, elapsedCompTime))

            # remove some_file: output from C compilers
            if is_c_test:
              for arg in args:
                if arg.endswith(".c"):
                  # remove lines like
                  # somefile.c:
                  # that some C compilers emit when compiling multiple files
                  output = output.replace(arg + ":\n", "");

            if (status != 0 or not executebin):
                # Save original output
                origoutput = output;

                # Compare compiler output with expected program output
                if catfiles:
                    logger.write('[Concatenating extra files: %s]'%
                                     (test_filename+'.catfiles'))
                    logger.flush()
                    output+=subprocess.Popen(['cat']+catfiles.split(),
                                             stdout=subprocess.PIPE,
                                             stderr=subprocess.STDOUT).communicate()[0]

                # Sadly these scripts require an actual file
                complogfile=file(complog, 'w')
                complogfile.write('%s'%(output))
                complogfile.close()

                if globalPrediff:
                    logger.write('[Executing ./PREDIFF]')
                    logger.flush()
                    subprocess.Popen(['./PREDIFF',
                                      execname,complog,compiler,
                                      ' '.join(env_compopts)+' '+compopts,
                                      ' '.join(args)]).wait()

                if prediff:
                    logger.write('[Executing prediff %s.prediff]'%(test_filename))
                    logger.flush()
                    subprocess.Popen(['./'+test_filename+'.prediff',
                                      execname,complog,compiler,
                                      ' '.join(env_compopts)+' '+compopts,
                                      ' '.join(args)]).wait()

                
                # find the compiler .good file to compare against. The compiler
                # .good file can be of the form testname.<configuration>.good or
                # explicitname.<configuration>.good. It's not currently setup to
                # handle testname.<configuration>.<compoptsnum>.good, but that
                # would be easy to add. 
                basename = test_filename 
                if len(clist) != 0:
                    explicitcompgoodfile = clist[0].split('#')[1].strip()
                    basename = explicitcompgoodfile.replace('.good', '')

                goodfile = FindGoodFile(basename)

                if not os.path.isfile(goodfile) or not os.access(goodfile, os.R_OK):
                    logger.write('[Error cannot locate compiler output comparison file %s/%s]'%(localdir, goodfile))
                    logger.write('[Compiler output was as follows:]')
                    logger.write(origoutput)
                    cleanup(execname)
                    cleanup(printpassesfile)
                    continue # on to next compopts

                result = DiffFiles(goodfile, complog)
                if result == 0:
                    os.unlink(complog)
                    loggerout = '%s[Success '%(futuretest)
                else:
                    loggerout = '%s[Error '%(futuretest)
                loggerout += ('matching compiler output for %s/%s'%
                                     (localdir, test_filename))
                loggerout += printTestVariation(compoptsnum, compoptslist);
                logger.write('{}]'.format(loggerout))

                if (result != 0 and futuretest != ''):
                    badfile=test_filename+'.bad'
                    if os.access(badfile, os.R_OK):
                        badresult = DiffBadFiles(badfile, complog)
                        if badresult == 0:
                            os.unlink(complog);
                            loggerout = '[Clean match against .bad file '
                        else:
                            # bad file doesn't match, which is bad
                            loggerout = '[Error matching .bad file '
                        loggerout += 'for %s/%s'%(localdir, test_filename)
                        loggerout += printTestVariation(compoptsnum, compoptslist)
                        logger.write('{}]'.format(loggerout))

                cleanup(execname)
                cleanup(printpassesfile)
                continue # on to next compopts
            else:
                compoutput = output # save for diff

                exec_log_names = []

                # Exactly one execution output file.
                if len(compoptslist) == 1 and len(execoptslist) == 1:
                    exec_log_names.append(get_exec_log_name(execname))

                # One execution output file for the current compiler opt.
                elif len(compoptslist) > 1 and len(execoptslist) == 1:
                    exec_opts_num_tmp = 1
                    if execoptslist[0] == ' ':
                        exec_opts_num_tmp = 0
                    exec_log_names.append(get_exec_log_name(execname, compoptsnum, exec_opts_num_tmp))

                # One execution output file for each of the execution opts.
                elif len(compoptslist) == 1 and len(execoptslist) > 1:
                    for i in xrange(1, len(execoptslist) + 1):
                        exec_log_names.append(get_exec_log_name(execname, compoptsnum, i))

                # This enumerates the cross product of all compiler and execution
                # opts. It's not clear whether this is actually supported elsewhere
                # (like start_test), but it's here.
                else:
                    for i in xrange(1, len(execoptslist) + 1):
                        exec_log_names.append(get_exec_log_name(execname, compoptsnum, i))

                # Write the log(s), so it/they can be modified by preexec.
                for exec_log_name in exec_log_names:
                    with open(exec_log_name, 'w') as execlogfile:
                        execlogfile.write(compoutput)

            #
            # Compile successful
            #
            logger.write('[Success compiling %s/%s]'%(localdir, test_filename))

            # Note that compiler performance only times successful compilations. 
            # Tests that are designed to fail before compilation is complete will 
            # not get timed, so the total time compiling might be off slightly.   
            if compperftest and not is_c_test:
                # make the compiler performance directories if they don't exist 
                timePasses = True
                if not os.path.isdir(compperfdir) and not os.path.isfile(compperfdir):
                    os.makedirs(compperfdir)
                if not os.access(compperfdir, os.R_OK|os.X_OK):
                    logger.write('[Error creating compiler performance test directory %s]'%(compperfdir))
                    timePasses = False

                if not os.path.isdir(tempDatFilesDir) and not os.path.isfile(tempDatFilesDir):
                    os.makedirs(tempDatFilesDir)
                if not os.access(compperfdir, os.R_OK|os.X_OK):
                    logger.write('[Error creating compiler performance temp dat file test directory %s]'%(tempDatFilesDir))
                    timePasses = False

                # so long as we have to the directories 
                if timePasses: 
                    # We need to name the files differently for each compiler
                    # option. 0 is the default compoptsnum if there are no options
                    # listed so we don't need to clutter the names with that
                    compoptsstring = str(compoptsnum)
                    if compoptsstring == '0':
                        compoptsstring = ''

                    # make the datFileName the full path with / replaced with ~~ so
                    # we can keep the full path for later but not create a bunch of
                    # new directories.
                    datFileName = localdir.replace('/', '~~') + '~~' + test_filename + compoptsstring

                    # computePerfStats for the current test
                    logger.write('[Executing computePerfStats %s %s %s %s %s]'%(datFileName, tempDatFilesDir, keyfile, printpassesfile, 'False'))
                    logger.flush()
                    p = subprocess.Popen([utildir+'/test/computePerfStats', datFileName, tempDatFilesDir, keyfile, printpassesfile, 'False'], stdout=subprocess.PIPE)
                    compkeysOutput = p.communicate()[0]
                    datFiles = [tempDatFilesDir+'/'+datFileName+'.dat',  tempDatFilesDir+'/'+datFileName+'.error']
                    status = p.returncode

                    if status == 0:
                        logger.write('[Success finding compiler performance keys for %s/%s]'% (localdir, test_filename))
                    else:
                        logger.write('[Error finding compiler performance keys for %s/%s.]'% (localdir, test_filename))
                        printTestVariation(compoptsnum, compoptslist);
                        logger.write('computePerfStats output was:\n%s'%(compkeysOutput))
                        logger.flush()
                        logger.write('Deleting .dat files for %s/%s because of failure to find all keys'%(localdir, test_filename))
                        for datFile in datFiles:
                            if os.path.isfile(datFile):
                                os.unlink(datFile)

                #delete the timing file     
                cleanup(printpassesfile)


            if st_args.comp_only:
                logger.write('[Note: Not executing or comparing the output due to -noexec flags]')
                cleanup(execname)
                continue # on to next compopts
            explicitcompgoodfile = None
            # Execute the test for all requested execopts
            execoptsnum = 0
            if len(clist)!=0:
                if len(clist[0].split('#')) > 1:
                    explicitcompgoodfile = clist[0].split('#')[1].strip()
            redirectin_set_in_loop = False
            redirectin_original_value = redirectin
            for texecopts in execoptslist:
                logger.flush()

                # Reset redirectin, in case execopts has multiple lines with
                # different stdin files.
                if redirectin_set_in_loop:
                    redirectin = redirectin_original_value
                    redirectin_set_in_loop = False
                if (len(compoptslist)==1) and (len(execoptslist)==1):
                    onlyone = True
                    execlog = get_exec_log_name(execname)
                else:
                    onlyone = False
                    if texecopts != ' ':
                        execoptsnum += 1
                    execlog = get_exec_log_name(execname, compoptsnum, execoptsnum)

                tlist = texecopts.split('#')
                execopts = tlist[0].strip()

                if numlocexecopts != None:
                    execopts += numlocexecopts;
                if len(tlist) > 1:
                    # Ignore everything after the first token
                    explicitexecgoodfile = tlist[1].strip().split()[0]
                else:
                    explicitexecgoodfile = explicitcompgoodfile
                del tlist

                if systemPreexec:
                    logger.write('[Executing system-wide preexec]')
                    logger.flush()
                    subprocess.Popen([systemPreexec,
                                      execname,execlog,compiler]).wait()

                if globalPreexec:
                    logger.write('[Executing ./PREEXEC]')
                    logger.flush()
                    subprocess.Popen(['./PREEXEC',
                                      execname,execlog,compiler]).wait()

                if preexec:
                    logger.write('[Executing preexec %s.preexec]'%(test_filename))
                    logger.flush()
                    subprocess.Popen(['./'+test_filename+'.preexec',
                                      execname,execlog,compiler]).wait()

                pre_exec_output = ''
                if os.path.exists(execlog):
                    with open(execlog, 'r') as exec_log_file:
                        pre_exec_output = exec_log_file.read()

                if not os.access(execname, os.R_OK|os.X_OK):
                    loggerout = ('%s[Error could not locate executable %s for %s/%s'%
                                     (futuretest, execname, localdir, test_filename))
                    loggerout += printTestVariation(compoptsnum, compoptslist,
                                       execoptsnum, execoptslist)
                    logger.write('{}]'.format(loggerout))
                    break; # on to next compopts

                # When doing whole program execution, we want to time the _real
                # binary for launchers that use a queue so we don't include the
                # time to get the reservation. These are the launchers known to
                # support timing the _real using CHPL_LAUNCHER_REAL_WRAPPER.
                timereal = chpllauncher in ['pbs-aprun', 'aprun', 'slurm-srun']

                args=list()
                if timer and timereal:
                    cmd='./'+execname
                    os.environ['CHPL_LAUNCHER_REAL_WRAPPER'] = timer
                elif timer:
                    cmd=timer
                    args+=['./'+execname]
                elif valgrindbin:
                    cmd=valgrindbin
                    args+=valgrindbinopts+['./'+execname]
                else:
                    cmd='./'+execname

                # if we're using a launchcmd, build up the command to call
                # launchcmd, and have it run the cmd and args built above
                if launchcmd:
                    # have chpl_launchcmd time execution and place results in a
                    # file since sub_test time will include time to get reservation
                    launchcmd_exec_time_file = execname + '_launchcmd_exec_time.txt'
                    os.environ['CHPL_LAUNCHCMD_EXEC_TIME_FILE'] = launchcmd_exec_time_file

                    # save old cmd and args and add them after launchcmd st_args.
                    oldcmd = cmd
                    oldargs = list(args)
                    launch_cmd_list = shlex.split(launchcmd)
                    cmd = launch_cmd_list[0]
                    args = launch_cmd_list[1:]
                    args += [oldcmd]
                    args += oldargs

                args+=globalExecopts
                args+=shlex.split(execopts)
                # envExecopts are meant for chpl programs, dont add them to C tests
                if not is_c_test and envExecopts != None:
                    args+=shlex.split(envExecopts)
                if lastexecopts:
                    args += lastexecopts

                if len(args) >= 2 and '<' in args:
                  redirIdx = st_args.index('<')
                  execOptRedirect = args[redirIdx + 1]
                  args.pop(redirIdx+1)
                  args.pop(redirIdx)
                  if redirectin == None:
                      # It is a little unfortunate that we compile the test only to skip it here.
                      # In order to prevent this, the logic for combining all the places execpopts
                      # come from and checking for '<' would have to be factored out or duplicated
                      logger.write('[Skipping test with stdin redirection ("<") in execopts since '
                            '-nostdinredirect is given {0}/{1}]'.format(localdir, test_filename))
                      break;
                  elif redirectin == "/dev/null":
                    if os.access(execOptRedirect, os.R_OK):
                      redirectin = execOptRedirect
                      redirectin_set_in_loop = True
                    else:
                      logger.write('[Error: redirection file %s does not exist]'%(execOptRedirect))
                      break
                  else:
                    logger.write('[Error: a redirection file already exists: %s]'%(redirectin))
                    break

                #
                # Run program (with timeout)
                #
                for count in xrange(numTrials):
                    exectimeout = False  # 'exectimeout' is specific to one trial of one execopt setting
                    launcher_error = ''  # used to suppress output/timeout errors whose root cause is a launcher error
                    loggerout = '[Executing program %s %s'%(cmd, ' '.join(args))
                    if redirectin:
                        loggerout += ' < %s'%(redirectin)
                    logger.write('{}]'.format(loggerout))
                    logger.flush()

                    execStart = time.time()
                    if useLauncherTimeout:
                        if redirectin == None:
                            my_stdin = None
                        else:
                            my_stdin=file(redirectin, 'r')
                        test_command = [cmd] + args + LauncherTimeoutArgs(timeout)
                        p = subprocess.Popen(test_command,
                                            env=dict(os.environ.items() + testenv.items()),
                                            stdin=my_stdin,
                                            stdout=subprocess.PIPE,
                                            stderr=subprocess.STDOUT)
                        output = p.communicate()[0]
                        status = p.returncode

                        if re.search('slurmstepd: Munge decode failed: Expired credential', output, re.IGNORECASE) != None:
                            launcher_error = 'Jira 18 -- Expired slurm credential for'
                        elif re.search('output file from job .* does not exist', output, re.IGNORECASE) != None:
                            launcher_error = 'Jira 17 -- Missing output file for'
                        elif (re.search('PBS: job killed: walltime', output, re.IGNORECASE) != None or
                              re.search('slurm.* CANCELLED .* DUE TO TIME LIMIT', output, re.IGNORECASE) != None):
                            exectimeout = True
                            launcher_error = 'Timed out executing program'

                        if launcher_error:
                            loggerout = ('%s[Error: %s %s/%s'%
                                            (futuretest, launcher_error, localdir, test_filename))
                            loggerout += printTestVariation(compoptsnum, compoptslist,
                                               execoptsnum, execoptslist);
                            logger.write('{}]'.format(loggerout))
                            logger.write('[Execution output was as follows:]')
                            logger.write(trim_output(output))

                    elif useTimedExec:
                        wholecmd = cmd+' '+' '.join(map(ShellEscape, args))

                        if redirectin == None:
                            my_stdin = sys.stdin
                        else:
                            my_stdin = file(redirectin, 'r')
                        p = subprocess.Popen([timedexec, str(timeout), wholecmd],
                                            env=dict(os.environ.items() + testenv.items()),
                                            stdin=my_stdin,
                                            stdout=subprocess.PIPE,
                                            stderr=subprocess.STDOUT)
                        output = p.communicate()[0]
                        status = p.returncode

                        if status == 222:
                            exectimeout = True
                            loggerout = ('%s[Error: Timed out executing program %s/%s'%
                                            (futuretest, localdir, test_filename))
                            loggerout += printTestVariation(compoptsnum, compoptslist,
                                               execoptsnum, execoptslist);
                            logger.write('{}]'.format(loggerout))
                            logger.write('[Execution output was as follows:]')
                            logger.write(trim_output(output))
                        else:
                            # for perf runs print out the 5 processes with the
                            # highest cpu usage. This should help identify if other
                            # processes might have interfered with a test.
                            if perftest:
                                logger.write('[Reporting processes with top 5 highest cpu usages]')
                                logger.flush()
                                psCom = 'ps ax -o user,pid,pcpu,command '
                                subprocess.call(psCom + '| head -n 1', shell=True)
                                subprocess.call(psCom + '| tail -n +2 | sort -r -k 3 | head -n 5', shell=True)


                    else:
                        if redirectin == None:
                            my_stdin = None
                        else:
                            my_stdin=file(redirectin, 'r')
                        p = subprocess.Popen([cmd]+args,
                                            env=dict(os.environ.items() + testenv.items()),
                                            stdin=my_stdin,
                                            stdout=subprocess.PIPE,
                                            stderr=subprocess.STDOUT)
                        try:
                            output = SuckOutputWithTimeout(p.stdout, timeout)
                        except ReadTimeoutException:
                            exectimeout = True
                            loggerout = ('%s[Error: Timed out executing program %s/%s'%
                                            (futuretest, localdir, test_filename))
                            loggerout += printTestVariation(compoptsnum, compoptslist,
                                               execoptsnum, execoptslist);
                            logger.write('{}]'.format(loggerout))
                            KillProc(p, killtimeout)

                        status = p.returncode

                    elapsedExecTime = time.time() - execStart
                    test_name = os.path.join(localdir, test_filename)
                    compExecStr = ''
                    if compoptsnum != 0:
                        compExecStr += 'compopts: {0} '.format(compoptsnum)
                    if execoptsnum != 0:
                        compExecStr += 'execopts: {0}'.format(execoptsnum)
                    if compExecStr:
                        test_name += ' ({0})'.format(compExecStr.strip())

                    if launchcmd and os.path.exists(launchcmd_exec_time_file):
                        with open(launchcmd_exec_time_file, 'r') as fp:
                            try:
                                launchcmd_exec_time = float(fp.read())
                                logger.write('[launchcmd reports elapsed execution time '
                                    'for "{0}" - {1:.3f} seconds]'
                                    .format(test_name, launchcmd_exec_time))
                            except ValueError:
                                logger.write('Could not parse launchcmd time file '
                                    '{0}'.format(launchcmd_exec_time_file))
                        os.unlink(launchcmd_exec_time_file)

                    logger.write('[Elapsed execution time for "{0}" - {1:.3f} '
                        'seconds]'.format(test_name, elapsedExecTime))

                    if execTimeWarnLimit and elapsedExcTime > execTimeWarnLimit:
                        logger.write('[Warning: %s/%s took over %.0f seconds to '
                            'execute]' %(localdir, test_filename, execTimeWarnLimit))

                    if catfiles:
                        logger.write('[Concatenating extra files: %s]'%
                                        (test_filename+'.catfiles'))
                        logger.flush()
                        output+=subprocess.Popen(['cat']+catfiles.split(),
                                                stdout=subprocess.PIPE,
                                                stderr=subprocess.STDOUT).communicate()[0]

                    # Sadly the scripts used below require an actual file
                    with open(execlog, 'w') as execlogfile:
                        execlogfile.write(pre_exec_output)
                        execlogfile.write(output)

                    if not exectimeout and not launcher_error:
                        if systemPrediff:
                            logger.write('[Executing system-wide prediff]')
                            logger.flush()
                            logger.write(subprocess.Popen([systemPrediff,
                                                              execname,execlog,compiler,
                                                              ' '.join(env_compopts)+
                                                              ' '+compopts,
                                                              ' '.join(args)],
                                                              stdout=subprocess.PIPE).
                                            communicate()[0])

                        if globalPrediff:
                            logger.write('[Executing ./PREDIFF]')
                            logger.flush()
                            logger.write(subprocess.Popen(['./PREDIFF',
                                                              execname,execlog,compiler,
                                                              ' '.join(env_compopts)+
                                                              ' '+compopts,
                                                              ' '.join(args)],
                                                              stdout=subprocess.PIPE).
                                            communicate()[0])

                        if prediff:
                            logger.write('[Executing prediff ./%s]'%(prediff))
                            logger.flush()
                            logger.write(subprocess.Popen(['./'+prediff,
                                                              execname,execlog,compiler,
                                                              ' '.join(env_compopts)+
                                                              ' '+compopts,
                                                              ' '.join(args)],
                                                              stdout=subprocess.PIPE).
                                            communicate()[0])

                        if not perftest:
                            # find the good file 

                            basename = test_filename
                            commExecNum = ['']

                            # if there were multiple compopts/execopts find the
                            # .good file that corresponds to that run 
                            if not onlyone:
                                commExecNum.insert(0,'.'+str(compoptsnum)+'-'+str(execoptsnum))

                            # if the .good file was explicitly specified, look for
                            # that version instead of the multiple
                            # compopts/execopts or just the base .good file 
                            if explicitexecgoodfile != None:
                                basename  = explicitexecgoodfile.replace('.good', '')
                                commExecNum = ['']

                            execgoodfile = FindGoodFile(basename, commExecNum)

                            if not os.path.isfile(execgoodfile) or not os.access(execgoodfile, os.R_OK):
                                logger.write('[Error cannot locate program output comparison file %s/%s]'%(localdir, execgoodfile))
                                logger.write('[Execution output was as follows:]')
                                exec_output = subprocess.Popen(['cat', execlog],
                                    stdout=subprocess.PIPE).communicate()[0]
                                logger.write(trim_output(exec_output))

                                continue # on to next execopts

                            result = DiffFiles(execgoodfile, execlog)
                            if result == 0:
                                os.unlink(execlog)
                                loggerout = '%s[Success '%(futuretest)
                            else:
                                loggerout = '%s[Error '%(futuretest)
                            loggerout += ('matching program output for %s/%s'%
                                            (localdir, test_filename))
                            if result != 0:
                                a = printTestVariation(compoptsnum, 
                                        compoptslist, execoptsnum, execoptslist);
                                print(a)
                                loggerout += a
                            logger.write('{}]'.format(loggerout))

                            if (result != 0 and futuretest != ''):
                                badfile=test_filename+'.bad'
                                if os.access(badfile, os.R_OK):
                                    badresult = DiffFiles(badfile, execlog)
                                    if badresult == 0:
                                        os.unlink(execlog);
                                        loggerout = '[Clean match against .bad file '
                                    else:
                                        # bad file doesn't match, which is bad
                                        loggerout = '[Error matching .bad file '
                                    loggerout += 'for %s/%s'%(localdir, test_filename)
                                    loggerout += printTestVariation(compoptsnum, compoptslist);
                                    logger.write('{}]'.format(loggerout));


                    if perftest:
                        if not os.path.isdir(perfdir) and not os.path.isfile(perfdir):
                            os.makedirs(perfdir)
                        if not os.access(perfdir, os.R_OK|os.X_OK):
                            logger.write('[Error creating performance test directory %s]'%(perfdir))
                            break # on to next compopts

                        global keyfile
                        if explicitexecgoodfile == None:
                            perfexecname = test_filename
                            keyfile = PerfTFile(test_filename,'keys') #e.g. .perfkeys
                        else:
                            perfexecname = re.sub(r'\{0}$'.format(PerfSfx('keys')), '', explicitexecgoodfile)
                            if os.path.isfile(explicitexecgoodfile):
                                keyfile = explicitexecgoodfile
                            else:
                                keyfile = PerfTFile(test_filename,'keys')

                        perfdate = os.getenv('CHPL_TEST_PERF_DATE')
                        if perfdate == None:
                            perfdate = datetime.date.today().strftime("%m/%d/%y")

                        logger.write('[Executing %s/test/computePerfStats %s %s %s %s %s %s]'%(utildir, perfexecname, perfdir, keyfile, execlog, str(exectimeout), perfdate))
                        logger.flush()

                        p = subprocess.Popen([utildir+'/test/computePerfStats',
                                              perfexecname, perfdir, keyfile, execlog, str(exectimeout), perfdate],
                                             stdout=subprocess.PIPE)
                        logger.write('%s'%(p.communicate()[0]))
                        logger.flush()

                        status = p.returncode
                        if not exectimeout and not launcher_error:
                            if status == 0:
                                os.unlink(execlog)
                                loggerout = '%s[Success '%(futuretest)
                            else:
                                loggerout = '%s[Error '%(futuretest)
                            loggerout += ('matching performance keys for %s/%s'%
                                            (localdir, test_filename))
                            if status != 0:
                                loggerout += printTestVariation(compoptsnum, 
                                        compoptslist, execoptsnum, execoptslist);
                            logger.write('{}]'.format(loggerout))

                        if exectimeout or status != 0:
                            break

            cleanup(execname)

        del execoptslist
        del compoptslist

        elapsedCurFileTestTime = time.time() - curFileTestStart
        test_name = os.path.join(localdir, test_filename)
        logger.write('[Elapsed time to compile and execute all versions of "{0}" - '
            '{1:.3f} seconds]'.format(test_name, elapsedCurFileTestTime))


@atexit.register
def elapsed_sub_test_time():
    if not RUNNING:
        return

    """Print elapsed time for sub_test call to console."""
    global sub_test_start_time, localdir
    elapsed_sec = time.time() - sub_test_start_time

    test_name = localdir
    if 'CHPL_ONETEST' in os.environ:
        chpl_name = os.environ.get('CHPL_ONETEST')
        base_name = os.path.splitext(chpl_name)[0]
        test_name = os.path.join(test_name, base_name)

    logger.write('[Finished subtest "{0}" - {1:.3f} seconds]'.format(test_name, elapsed_sec))



#
# Time out class:  Read from a stream until time out
#  A little ugly but sending SIGALRM (or any other signal) to Python
#   can be unreliable (will not respond if holding certain locks).
#
class ReadTimeoutException(Exception): pass

def SetNonBlock(stream):
    flags = fcntl.fcntl(stream.fileno(), fcntl.F_GETFL)
    flags |= os.O_NONBLOCK
    fcntl.fcntl(stream.fileno(), fcntl.F_SETFL, flags)

def SuckOutputWithTimeout(stream, timeout):
    SetNonBlock(stream)
    buffer = ''
    end_time = time.time() + timeout
    while True:
        now = time.time()
        if end_time <= now:
            # Maybe return partial result instead?
            raise ReadTimeoutException('Teh tiem iz out!');
        ready_set = select.select([stream], [], [], end_time - now)[0]
        if stream in ready_set:
            bytes = stream.read()
            if len(bytes) == 0:
                break           # EOF
            buffer += bytes     # Inefficient way to accumulate bytes.
            # len(ready_set) == 0 is also an indication of timeout. However,
            # if we relied on that, we would require no data ready in order
            # to timeout  which doesn't seem quite right either.
    return buffer

def LauncherTimeoutArgs(seconds):
    if useLauncherTimeout == 'pbs' or useLauncherTimeout == 'slurm':
        # --walltime=hh:mm:ss
        m, s = divmod(seconds, 60)
        h, m = divmod(m, 60)
        fmttime = '--walltime={0:02d}:{1:02d}:{2:02d}'.format(h, m, s)
        return [fmttime]
    else:
        Fatal('LauncherTimeoutArgs encountered an unknown format spec: ' + \
              useLauncherTimeout)


#
# Auxilliary functions
#

# Escape all special characters
def ShellEscape(arg):
    return re.sub(r'([\\!@#$%^&*()?\'"|<>[\]{} ])', r'\\\1', arg)

# Escape all special characters but leave spaces alone
def ShellEscapeCommand(arg):
    return re.sub(r'([\\!@#$%^&*()?\'"|<>[\]{}])', r'\\\1', arg)


# Grabs the start and end of the output and replaces non-printable chars with ~
def trim_output(output):
    max_size = 256*1024 # ~1/4 MB
    if len(output) > max_size:
        new_output = output[:max_size/2]
        new_output += output[-max_size/2:]
        output = new_output
    return ''.join(s if s in string.printable else "~" for s in output)


# return True if f has .chpl extension
def IsChplTest(f):
    if re.match(r'^.+\.(chpl|test\.c)$', f):
        return True
    else:
        return False

perflabel = '' # declare it for the following functions

# file suffix: 'keys' -> '.perfkeys' etc.
def PerfSfx(s):
    return '.' + perflabel + s

# directory-wide file: 'COMPOPTS' or 'compopts' -> './PERFCOMPOPTS' etc.
def PerfDirFile(s):
    return './' + perflabel.upper() + s.upper()

# test-specific file: (foo,keys) -> foo.perfkeys etc.
def PerfTFile(test_filename, sfx):
    return test_filename + '.' + perflabel + sfx

# read file with comments
def ReadFileWithComments(f, ignoreLeadingSpace=True):
    with open(f, 'r') as myfile:
      mylines = myfile.readlines()
    mylist=list()
    for line in mylines:
        line = line.rstrip()
        # ignore blank lines
        if not line.strip(): continue
        # ignore comments
        if ignoreLeadingSpace:
            if line.lstrip()[0] == '#': continue
        else:
            if line[0] == '#': continue
        # expand shell variables
        line = os.path.expandvars(line)
        mylist.append(line)
    return mylist

# diff 2 files
def DiffFiles(f1, f2):
    logger.write('[Executing diff %s %s]'%(f1, f2))
    p = subprocess.Popen(['diff',f1,f2],
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    myoutput = p.communicate()[0] # grab stdout to avoid potential deadlock
    if p.returncode != 0:
        logger.write(trim_output(myoutput))
    return p.returncode

# diff output vs. .bad file, filtering line numbers out of error messages that arise
# in module files.
def DiffBadFiles(f1, f2):
    logger.write('[Executing diff %s %s]'%(f1, f2))
    p = subprocess.Popen([utildir+'/test/diff-ignoring-module-line-numbers', f1, f2],
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    myoutput = p.communicate()[0] # grab stdout to avoid potential deadlock
    if p.returncode != 0:
        logger.write(myoutput)
    return p.returncode

# kill process
def KillProc(p, timeout):
    k = subprocess.Popen(['kill',str(p.pid)])
    k.wait()
    now = time.time()
    end_time = now + timeout # give it a little time
    while end_time > now:
        if p.poll():
            return
        now = time.time()
    # use the big hammer (and don't bother waiting)
    subprocess.Popen(['kill','-9', str(p.pid)])
    return

# clean up after the test has been built
def cleanup(execname):
    try:
        if execname is not None:
            if os.path.isfile(execname):
                os.unlink(execname)
            if os.path.isfile(execname+'_real'):
                os.unlink(execname+'_real')
    except (IOError, OSError) as ex:
        # If the error is "Device or resource busy", call lsof on the file (or
        # handle for windows) to see what is holding the file handle, to help
        # debug the issue.
        if isinstance(ex, OSError) and ex.errno == 16:
            handle = which('handle')
            lsof = which('lsof')
            if handle is not None:
                logger.write('[Inspecting open file handles with: {0}'.format(handle))
                subprocess.Popen([handle]).communicate()
            elif lsof is not None:
                cmd = [lsof, execname]
                logger.write('[Inspecting open file handles with: {0}'.format(' '.join(cmd)))
                subprocess.Popen(cmd).communicate()

        # Do not print the warning for cygwin32 when errno is 16 (Device or resource busy).
        if not (getattr(ex, 'errno', 0) == 16 and platform == 'cygwin32'):
            logger.write('[Warning: could not remove {0}: {1}]'.format(execname, ex))

def which(program):
    """Returns absolute path to program, if it exists in $PATH. If not found,
    returns None.

    From: http://stackoverflow.com/a/377028
    """
    def is_exe(fpath):
        return os.path.isfile(fpath) and os.access(fpath, os.X_OK)

    fpath, fname = os.path.split(program)
    if fpath:
        if is_exe(program):
            return program
    else:
        for path in os.environ.get('PATH', '').split(os.pathsep):
            path = path.strip('"')
            exe_file = os.path.join(path, program)
            if is_exe(exe_file):
                return exe_file
    return None


# print (compopts: XX, execopts: XX) for later decoding of failed tests
def printTestVariation(compoptsnum, compoptslist,
                       execoptsnum=0, execoptslist=[] ):
    printCompOpts = True
    printExecOpts = True
    loggerout = ""
    if compoptsnum == 0 or len(compoptslist) <= 1:
        printCompOpts = False
    if execoptsnum == 0 or len(execoptslist) <= 1:
        printExecOpts = False

    if (not printCompOpts) and (not printExecOpts):
        return loggerout;

    loggerout += ' ('
    if printCompOpts:
        loggerout += 'compopts: %d'%(compoptsnum)
    if printExecOpts:
        if printCompOpts:
            loggerout += ', '
        loggerout += 'execopts: %d'%(execoptsnum)
    loggerout += ')'
    return loggerout

# return true if string is an integer
def IsInteger(str):
    try:
        int(str)
        return True
    except ValueError:
        return False

# read integer value from a file
def ReadIntegerValue(f, localdir):
    to = ReadFileWithComments(f)
    if to:
        for l in to:
            if l[0] == '#':
                continue
            if IsInteger(l):
                return string.atoi(l)
            else:
                break
    Fatal('Invalid integer value in '+f+' ('+localdir+')')

# report an error message and exit
def Fatal(message):
    logger.write('[Error (sub_test): '+message+']')
    magic_exit_code = reduce(operator.add, map(ord, 'CHAPEL')) % 256
    sys.exit(magic_exit_code)

# Attempts to find an appropriate timer to use. The timer must be in
# util/test/timers/. Expects to be passed a file containing only the name of
# the timer script. If the file is improperly formatted the default timer is
# used, and if the timer is not executable or can't be found 'time -p' is used
def GetTimer(f):
    timersdir = os.path.join(utildir, 'test', 'timers')
    defaultTimer = os.path.join(timersdir, 'defaultTimer')

    lines = ReadFileWithComments(f)
    if len(lines) != 1:
        logger.write('[Error "%s" must contain exactly one non-comment line '
            'with the name of the timer located in %s to use. Using default ' 
            'timer %s.]' %(f, timersdir, defaultTimer))
        timer = defaultTimer
    else:
        timer = os.path.join(timersdir, lines[0])

    if not os.access(timer,os.R_OK|os.X_OK):
        logger.write('[Error cannot execute timer "%s", using "time -p"]' %(timer))
        return 'time -p'

    return timer

# attempts to find an appropriate .good file. Good files are expected to be of
# the form basename.<configuration>.<commExecNums>.good. Where configuration
# options are one of the below configuration specific parameters that are
# checked for. E.G the current comm layer. commExecNums are the optional
# compopt and execopt number to enable different .good files for different
# compopts/execopts with explicitly specifying name. 
def FindGoodFile(basename, commExecNums=['']):
    
    goodfile = ''
    for commExecNum in commExecNums:
        # Try the machine specific .good
        if not os.path.isfile(goodfile):
            goodfile = basename+'.'+machine+commExecNum+'.good'
        # Else if --no-local try the no-local .good file.
        if not os.path.isfile(goodfile):
            if '--no-local' in env_compopts:
                goodfile=basename+'.no-local'+commExecNum+'.good'
        # Else try comm and locale model specific .good file.
        if not os.path.isfile(goodfile):
            goodfile=basename+chplcommstr+chpllmstr+commExecNum+'.good'
        # Else try the comm-specific .good file.
        if not os.path.isfile(goodfile):
            goodfile=basename+chplcommstr+commExecNum+'.good'
        # Else try locale model specific .good file.
        if not os.path.isfile(goodfile):
            goodfile=basename+chpllmstr+commExecNum+'.good'
        # Else try the platform-specific .good file.
        if not os.path.isfile(goodfile):
            goodfile=basename+'.'+platform+commExecNum+'.good'
        # Else use the execopts-specific .good file.
        if not os.path.isfile(goodfile):
            goodfile=basename+commExecNum+'.good'

    return goodfile

def get_exec_log_name(execname, comp_opts_count=None, exec_opts_count=None):
    """Returns the execution output log name based on number of comp and exec opts."""
    suffix = '.exec.out.tmp'
    if comp_opts_count is None and exec_opts_count is None:
        return '{0}{1}'.format(execname, suffix)
    else:
        return '{0}.{1}-{2}{3}'.format(execname, comp_opts_count, exec_opts_count, suffix)

# If the first line of the skipif file contains '/usr/bin/env', then just execute it.
# (Don't forget to add execute permission to a script skipif file.)
# Otherwise, use testEnv to process it the old way.
def runSkipIf(skipifName):
    name = './' + skipifName
    # Already a file because os.R_OK is true?
    if os.access(name, os.X_OK):
        env_cmd = [os.path.join(utildir, 'printchplenv'), '--simple']
        chpl_env = subprocess.Popen(env_cmd, stdout=subprocess.PIPE).communicate()[0]
        chpl_env = dict(map(lambda l: l.split('='), chpl_env.splitlines()))

        skipif_env = os.environ.copy()
        skipif_env.update(chpl_env)
        skiptest = subprocess.Popen([name], stdout=subprocess.PIPE, env=skipif_env).communicate()[0]
    else:
        skiptest = subprocess.Popen([utildir+'/test/testEnv', './'+skipifName], stdout=subprocess.PIPE).communicate()[0]
    return skiptest

if __name__ == "main":
    run({})
