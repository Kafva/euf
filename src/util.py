import sys, os, re
from datetime import datetime

from clang import cindex
from src import ERR_EXIT

from src.config import CONFIG
from src.types import AnalysisResult, CbmcResult, FunctionResult

def add_to_timeout_blacklist(func_name:str) -> None:
    if CONFIG.ENABLE_TIMEOUT_BLACKLIST and \
     os.path.isdir(os.path.dirname(CONFIG.TIMEOUT_BLACKLIST_FILE)):
        print_info(f"Adding {func_name} to {CONFIG.TIMEOUT_BLACKLIST_FILE}")
        with open(CONFIG.TIMEOUT_BLACKLIST_FILE, mode='a', encoding='utf8') \
         as f:
            f.write(f"{func_name}\n")

def load_timeout_blacklist() -> set[str]:
    timed_out_functions = set()
    if CONFIG.ENABLE_TIMEOUT_BLACKLIST:
        if os.path.isfile(CONFIG.TIMEOUT_BLACKLIST_FILE):
            with open(CONFIG.TIMEOUT_BLACKLIST_FILE, mode = 'r', encoding='utf8') \
             as f:
                for line in f.readlines():
                    timed_out_functions.add(line.strip())
    return timed_out_functions

def ccdb_dir(new: bool) -> str:
    '''
    Retrieve the path to the 'project root' of the old or new version of the
    dependency _WITHOUT_ a trailing slash.
    The project root is defined as the directory with compile_commands.json
    and is usually the same as the .git directory.
    '''
    source_dir = CONFIG.DEP_SOURCE_ROOT.removeprefix(CONFIG.DEPENDENCY_DIR) \
        if CONFIG.DEP_SOURCE_ROOT != "" \
        else ""

    return f"{git_dir(new=new)}/{source_dir.lstrip('/')}".rstrip("/")

def git_dir(new: bool) -> str:
    '''
    Retrieve the path to the git worktree of either the new or old version
    of the dependency being analyzed WITHOUT a trailing "/"
    '''
    dep_name = os.path.basename(CONFIG.DEPENDENCY_DIR)

    return f"{CONFIG.EUF_CACHE}/{dep_name}-{CONFIG.COMMIT_NEW[:8]}" \
           if new else \
            f"{CONFIG.EUF_CACHE}/{dep_name}-{CONFIG.COMMIT_OLD[:8]}"

def git_relative_path(abspath: str):
    '''
    Returns the provided absolute path as a subpath relative to
    either the new/old dependency or the main project (depending on
    its prefix).
    '''
    rel_path = abspath.removeprefix(git_dir(new=False)). \
                   removeprefix(git_dir(new=True)). \
                   removeprefix(CONFIG.PROJECT_DIR). \
                   removeprefix(CONFIG.DEPENDENCY_DIR)
    return rel_path.lstrip("/")

def shorten_path_fields(csv:str, delim:str=";"):
    '''
    Attempt to convert each field that starts with a "/"
    into a git-relative path
    '''
    out = ""
    for field in csv.split(delim):
        if field.startswith("/"):
            out += git_relative_path(field) + delim
        else:
            out += field + delim

    return out[:-1] # Exclude last ';'

def wait_on_cr(always=False):
    while CONFIG.PAUSES or always:
        print("\033[32m\033[0m ", end='', file = sys.stderr, flush = True)
        if sys.stdin.readline() == "\n":
            break

def print_info(msg: str):
    if CONFIG.VERBOSITY >= 0:
        print("\033[34m!>\033[0m " +  msg, file=sys.stderr, flush=True)

def print_success(msg: str):
    print("[\033[32m+\033[0m] " +  msg, file=sys.stderr, flush=True)

def print_fail(msg: str):
    print("[\033[31mX\033[0m] " +  msg, file=sys.stderr, flush=True)

def print_inconclusive(msg: str):
    print("[\033[33m~\033[0m] " +  msg, file=sys.stderr, flush=True)

def print_warn(msg: str):
    if CONFIG.VERBOSITY >= 0:
        print("\033[33m!>\033[0m " +  msg, file=sys.stderr, flush=True)

def print_err(msg: str):
    print("\033[31m!>\033[0m " +  msg, file=sys.stderr, flush=True)

def print_stage(msg: str):
    print("\033[34m==>\033[0m " +  msg + " \033[34m<==\033[0m ",
        file=sys.stderr, flush=True)

def set_libclang():
    if not os.path.exists(CONFIG.LIBCLANG):
        found = False
        for fallback in CONFIG.LIBCLANG_FALLBACKS:
            if os.path.exists(fallback):
                CONFIG.LIBCLANG = fallback
                found = True
                break

        if not found:
            print_err("Missing path to libclang")
            sys.exit(ERR_EXIT)

    cindex.Config.set_library_file(CONFIG.LIBCLANG)

def flatten_dict(list_of_dicts: list[dict] ) -> dict:
    flat = {}
    for di in list_of_dicts:
        for key,val in di.items():
            if not key in flat:
                flat[key] = []
            flat[key].extend(val)

    return flat

def flatten(list_of_lists: list[list]) -> list:
    flat = []
    for li in list_of_lists:
        flat.extend(li)
    return flat

def get_column_counts(blob: str, column_index:int, sep:str = "") \
 -> list[tuple[str,int]]:
    '''
    Return the number of occurrences of each string in a newline separated file
    for a given separator and column index (zero based). Empty on failure
    '''
    column_stats = {}

    for line in blob.splitlines():
        try:
            if sep != "":
                column_value = line.split(sep)[column_index]
            else:
                column_value = line.split()[column_index]
        except (ValueError,IndexError):
            return []
        if column_value in column_stats:
            column_stats[column_value] += 1
        else:
            column_stats[column_value] = 1

    return list(column_stats.items())

def find(name, path) -> str:
    for root, _, files in os.walk(path):
        if name in files:
            return os.path.join(root, name)
    return ""

def time_start(msg: str) -> datetime:
    if CONFIG.VERBOSITY >= 1:
        print_info(msg)
    return datetime.now()

def print_result(msg: str, result = AnalysisResult.NONE) -> None:
    match result:
        case AnalysisResult.SUCCESS:
            print_success(msg)
        case AnalysisResult.SUCCESS_UNWIND_FAIL:
            print_inconclusive(msg)
        case AnalysisResult.FAILURE:
            print_fail(msg)
        case AnalysisResult.FAILURE_UNWIND_FAIL:
            print_inconclusive(msg)

        case AnalysisResult.NO_VCCS | AnalysisResult.NO_VCCS_UNWIND_FAIL:
            print_fail(msg)

        case AnalysisResult.NO_BODY:
            print_fail(msg)

        case AnalysisResult.STRUCT_CNT_CONFLICT:
            print_err(msg)
        case AnalysisResult.STRUCT_TYPE_CONFLICT:
            print_err(msg)
        case AnalysisResult.ERROR:
            print_err(msg)

        case AnalysisResult.NONE:
            print_info(msg)

        case _: # Default to warning
            print_warn(msg)

def time_end(msg: str, start_time: datetime,
 result: AnalysisResult = AnalysisResult.NONE) -> None:
    if CONFIG.VERBOSITY >= 1:
        print_result(f"{msg}: {datetime.now() - start_time}", result)
        start_time = datetime.now()

def mkdir_p(path: str):
    joined = ""
    for subpath in path.split('/')[1:]:

        joined += "/"+subpath

        if os.path.exists(joined) and not os.path.isdir(joined):
            print_err(f"Not a directory: {joined}")
            sys.exit(ERR_EXIT)
        elif not os.path.isdir(joined):
            os.mkdir(joined)

def rm_f(path: str):
    if os.path.isfile(path):
        os.remove(path)

def has_allowed_suffix(string, git_diff:bool=False) -> bool:
    whitelist = CONFIG.SUFFIX_WHITELIST_GIT_DIFF if git_diff \
            else CONFIG.SUFFIX_WHITELIST
    suffixes = "|".join(whitelist).strip("|").replace(".", "\\.")
    return re.match(rf".*({suffixes})$", string) is not None

def remove_files_in(path: str):
    if os.path.isdir(path):
        for file in os.listdir(path):
            filepath = f"{path}/{file}"
            if os.path.isfile(filepath):
                os.remove(filepath)

def load_cbmc_results(name:str, result_dir:str) -> \
 tuple[dict[str,FunctionResult],dict[str,list[CbmcResult]]]:
    '''
    Load the data from every cbmc.csv for a given case (libonig etc.)
    under the given result_dir.
    '''
    function_results_dict = {}
    cbmc_results_dict = {}

    for item in os.listdir(result_dir):
        dirpath = f"{result_dir}/{item}"

        # Only load entries matching the current name
        if os.path.isdir(dirpath) and item.startswith(name):
            cbmc_results_dict[dirpath] = load_cbmc_result(
                    dirpath,
                    function_results_dict
            )

            # For each cbmc.csv, add any new results for a function
            # to the dictionary of function_results
            for func_name,func_result in function_results_dict.items():
                # Full results
                func_result.results.extend(
                    map(lambda a: a.result, filter(lambda c:
                        not c.identity and c.func_name == func_name,
                        cbmc_results_dict[dirpath]
                    )
                ))
                # Identity results
                func_result.results_id.extend(
                    map(lambda a: a.result, filter(lambda c:
                        c.identity and c.func_name == func_name,
                        cbmc_results_dict[dirpath]
                    )
            ))

    return function_results_dict, cbmc_results_dict

def load_cbmc_result(dirpath:str, \
  function_results_dict: dict[str,FunctionResult]) -> list[CbmcResult]:
    '''
    Load each row of cbmc.csv from the provided dirpath into a list
    of CbmcResult objects and populate the provided dict with
    FunctionResults.
    '''
    cbmc_results = []

    if os.path.isfile(f"{dirpath}/cbmc.csv"):
        with open(f"{dirpath}/cbmc.csv", mode = 'r', encoding='utf8') as f:
            for line in f.readlines()[1:]:
                cbmc_results.append(
                    CbmcResult.new(line.split(";"), dirpath)
                )

                # Add a key for each encountered function name
                func_name = cbmc_results[-1].func_name
                if func_name not in function_results_dict:
                    function_results_dict[func_name] =\
                        FunctionResult(func_name=func_name)

    return cbmc_results

