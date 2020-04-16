import argparse
import fnmatch
from functools import partial
import json
import os
import sys
import re
import subprocess
import tempfile

def shell(cmd):
    """do command in shell (like os.system() but with capture output)"""
    cmdshow = cmd
    out = ''
    try:
        process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, stdin=subprocess.PIPE, shell=True, cwd=None)
        out = process.communicate()[0].replace(b'\r\n', b'\n')
    except Exception as err:
        raise RuntimeError(cmd, str(err), -1)
    if process.returncode != 0:
        raise RuntimeError(cmd, out, process.returncode)
    return out


def print_results(failed):
    def print_error(e):
        ee = e[1].split("\n")
        ret = ""
        ret = "executing: {0}, get ERROR:".format(e[0])
        for l in ee:
            ret += "\n"+l
        print(ret)

    if len(failed) > 0:
        for f in failed:
            print(os.path.join(f[1], f[0]) + "\n")
            print_error(f[2])
        print("FAILED TESTS: {0}".format(len(failed)))
    else:
        print("SUCCESS")

class ExtendAction(argparse.Action):
        def __call__(self, parser, namespace, values, option_string=None):
                items = getattr(namespace, self.dest) or []
                items.extend(values)
                setattr(namespace, self.dest, items)

_jpaths = os.path.join
quirrel_static_analyzer = "quirrel_static_analyzer"
csq_path = "csq"

def find_config_path(path, startpath="", config_name=".dreyconfig"):
    def rfind(path):
        configpath = _jpaths(path, config_name)
        if os.path.exists(configpath) and os.path.isfile(configpath):
            return configpath
        elif len(os.path.split(path)[1])>0:
            return rfind(os.path.split(path)[0])
        else:
            return None

    abspath = os.path.abspath(path)
    return rfind(abspath)

def loadconfig(path):
    if path is None:
        return None
    with open(path) as data_file:
        config = json.load(data_file)
        config["path_to_this_config"] = os.path.dirname(path)
        return config



def gather_files_in_predefinition_paths(config, config_path):
    if config is None:
        return None

    predefinition_paths = config.get("predefinition_paths", [])
    if len(predefinition_paths) == 0:
        return None

    list_file = tempfile.NamedTemporaryFile(mode = "wt", delete = False)
    print("Config Path: {0}\n".format(config_path))
    for pp in predefinition_paths:
        combined_path = os.path.normpath(os.path.join(config_path, pp))
        print("Collecting predefinition files at {0}\n".format(combined_path))
        if os.name == 'nt' :
            out = shell("call dir /b/s {0} | findstr \\.nut$".format(combined_path)).decode('utf-8')
        else:
            out = shell("find {0} -name \"*.nut\"".format(combined_path)).decode('utf-8')
        list_file.write(out)

    list_file.close()
    return list_file.name



def checkpath_by_config(config, config_path, p, root, isFile):
    if config is None and isFile:
        return False
    if config is not None and not config.get("enabled", True):
        return False
    if config is None and not isFile:
        config = {}
    dirs_to_skip = config.get("dirs_to_skip",[])
    files_to_skip = config.get("files_to_skip",[])
    if len(dirs_to_skip)+len(files_to_skip) == 0:
        return True
    path_rel_to_config = os.path.relpath(os.path.abspath(_jpaths(root, p)), os.path.dirname(config_path))
    path_rel_to_config = os.path.normpath(path_rel_to_config)
    dirs = os.path.dirname(path_rel_to_config).split(os.path.sep) if isFile else path_rel_to_config.split(os.path.sep)
    for pattern in dirs_to_skip:
        if len(fnmatch.filter(dirs, pattern))>0:
            return False
    if isFile:
        for pattern in files_to_skip:
            if fnmatch.fnmatch(os.path.basename(path_rel_to_config).lower(), pattern):
                return False
    return True

def get_all_files_by_extensions_and_dirs(files, dirs, extensions, exclude_dirs=["CVS",".git"], use_configs = True):
    def check_file_ext(file, extensions):
        textensions = tuple(extensions) if isinstance(extensions, list) else extensions
        return file.lower().endswith(textensions)

    collection = {}
    for f in files:
        assert os.path.isfile(f)
        configpath = find_config_path(os.path.dirname(f))
        config = loadconfig(configpath) if use_configs else {}
        collection.update({os.path.normpath(f):config})
    for path in dirs:
        for root, dirs, ffiles in os.walk(path):
            configpath = find_config_path(root)
            config = loadconfig(configpath) if use_configs else {}
            dirs[:] = [d for d in dirs if d not in exclude_dirs]
            dirs[:] = [d for d in dirs if checkpath_by_config(config, configpath, d, root, False)]
            ffiles[:] = [f for f in ffiles if check_file_ext(f, extensions)]
            ffiles[:] = [f for f in ffiles if checkpath_by_config(config, configpath, f, root, True)]
            pathfiles    = [os.path.abspath(os.path.normpath(os.path.join(root, f))) for f in ffiles]
            [collection.update({file:config}) for file in pathfiles]
    return collection

def gather_files(paths, use_configs = True):
    files = [f for f in paths if os.path.isfile(f)]
    dirs = [f for f in paths if os.path.isdir(f) ]
    assert (len(files)+len(dirs)) == len(paths), "inexisting path!"
    res = get_all_files_by_extensions_and_dirs(files, dirs, extensions = (".nut"), exclude_dirs=["CVS",".git"], use_configs = use_configs)
    return res

nametonummap = {}
def tidtocmd(tid):
    return "-w{0}".format(nametonummap.get(tid, tid))

def shell_test(cmd, extras=""):
    try:
        shell("{cmd} {extras}".format(cmd=cmd, extras=extras))
        return True
    except RuntimeError as e:
        return ("", "", e)

def run_tests_on_files(files, cmds):
    list_file = tempfile.NamedTemporaryFile(mode = "wt", delete = False)
    for item in files:
        list_file.write("%s\n" % item)
    list_file.close()
    failed = shell_test(
        "{0} {1} --csq-exe:{2} --files:{3}".format(quirrel_static_analyzer, cmds if isinstance(cmds, str) else " ".join(cmds), csq_path, list_file.name), "")
    failed = [] if failed == True else [failed]
    print_results(failed)
    try:
        os.remove(list_file.name)
    except:
        pass
    return failed


def check_files(files, cmdchecks = [], inverse_warnings = True, **kwargs):
    numtoname = dict(zip(nametonummap.values(), nametonummap.keys()))
    namedchecks = [nametonummap.get(k,numtoname.get(k, "-w{0}".format(k))) for k in cmdchecks]
    print("Check squirrel files")
    if inverse_warnings:
        print("Checks: {0}".format(" ".join(namedchecks)))
    else:
        if len(namedchecks) > 0:
            print("Disabled checks: {0}".format(" ".join(namedchecks) if namedchecks else "None"))
    cmdchecks = [tidtocmd(c) for c in cmdchecks]
    print("Checking files:\n    {0}{1}".format("\n    ".join(files.keys()[:10]), "\n        and {0} more".format(len(files)-10) if len(files) >10 else ""))

    extracmds = " ".join([ "--{0}:{1}".format(key.replace("_","-"),value) for key, value in list( kwargs.items() )])
    failed = run_tests_on_files(files.keys(), [" ".join(cmdchecks), " --inverse-warnings" if inverse_warnings else "", extracmds])
    if len(failed)>0:
        sys.exit(1)


def get_files_by_configs(table):
    res = {}
    for file, config in table.iteritems():
        if config is None:
            config = {}
        config_str = json.dumps(config) #.get("checks",[]))
        if not (os.path.basename(file) in config.get("files_to_skip",[])):
            if res.get(config_str) is not None:
                c = res[config_str]
                c.append(file)
                res[config_str] = c
            else:
                res[config_str] = [file]
    return res


def check_files_with_configs(files, cmdchecks = [], **kwargs):
    cfiles = get_files_by_configs(files)

    failed = []
    print("Check squirrel files using .dreyconfig files")
    for config_str, filesList in cfiles.iteritems():
        config = json.loads(config_str)
        configchecks = config.get("checks", [])

        totalchecks = configchecks + cmdchecks
        cmds = ""
        print("Checking files:\n    {0}{1}".format("\n    ".join(filesList[:10]), "\n        and {0} more".format(len(filesList)-10) if len(filesList) >10 else ""))
        if "*" in totalchecks:
            print("All warnings check enabled")
            cmds = ""
        else:
            disabled_checks = [k for k in nametonummap.keys() if k not in totalchecks]
            print("Disabled checks: {0}".format(" ".join(disabled_checks) if disabled_checks else "None"))
            totalchecks = [tidtocmd(c) for c in totalchecks]
            totalchecks = " ".join(totalchecks)
            cmds = "--inverse-warnings {0}".format(totalchecks)
        extracmds = " ".join([ "--{0}:{1}".format(key.replace("_","-"),value) for key, value in list( kwargs.items() )])


        predefinition_paths = config.get("predefinition_paths", [])
        config_path = config.get("path_to_this_config", "--unknown path--");
        pre_tmp_file_name = gather_files_in_predefinition_paths(config, config_path) if len(predefinition_paths) > 0 else None

        if pre_tmp_file_name != None:
            extracmds = "{0} --predefinition-files:{1}".format(extracmds, pre_tmp_file_name)

        failed.extend(run_tests_on_files(filesList, [cmds, extracmds]))

        if pre_tmp_file_name != None:
            os.remove(pre_tmp_file_name)

    print_results(failed)
    if len(failed)>0:
        sys.exit(1)


def getNameWarningMap():
    findre = re.compile("w(\d+)\s*\((.*)\)")
    out = shell("{0} --warnings-list".format(quirrel_static_analyzer)).decode('utf-8')
    out = out.splitlines()
    filtered = []
    for i, o in enumerate(out):
        if i%3==0:
            filtered.append(o)
    res = {}
    for f in filtered:
        m = findre.search(f)
        if m:
            res.update({m.group(2):m.group(1)})
    return res

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='style check')
    parser.register('action', 'extend', ExtendAction)
    parser.add_argument('paths', nargs='*', type=str, default = "")
    parser.add_argument('-w', '--warnings', nargs = '*', type=str, default = [], action="extend", help = "disable or enable checks by numeric warning like -w227 -w452. * is treated as 'all' warnings.")
    parser.add_argument('-u', '--use-configs', default = False, action="store_true", help = "use .dreyconfig files")
    parser.add_argument('-i', '--inverse-warnings', default = False, action="store_true", help = "check only specified warnings. Ignored work with --use-configs")
    parser.add_argument('-om', '--output-mode', action="store", default = "full", type = str, choices=["full", "2-lines", "1-line"])
    args = parser.parse_args()
    if len(sys.argv[1:])==0:
            #parser.print_help()
            parser.print_usage() # for just the usage line
            parser.exit()
    dagor2_dir = os.environ.get("DAGOR2_DIR")
    if dagor2_dir:
        sys.path.append(os.path.join(dagor2_dir,"tools","dagor3_cdk","util"))
    nametonummap = getNameWarningMap()
    use_configs = args.use_configs
    assert len(args.paths)>0
    files = gather_files(args.paths, use_configs)

    if args.use_configs:
        check_files_with_configs(files, args.warnings, output_mode = args.output_mode)
    else:
        check_files(files, args.warnings, args.inverse_warnings, output_mode = args.output_mode)

