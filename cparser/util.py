import sys, os, re
from datetime import datetime
from typing import Set

from cparser import CONFIG, AnalysisResult, print_warn, print_err

def wait_on_cr(always=False):
    while (CONFIG.PAUSES and not CONFIG.SHOW_DIFFS) or always:
        print("\033[32m\033[0m ", end='', file = sys.stderr, flush = True)
        if sys.stdin.readline() == "\n":
            break

def print_info(msg: str):
    print("\033[34m!>\033[0m " +  msg, file=sys.stderr)

def print_stage(msg: str):
    print("\033[34m==>\033[0m " +  msg + " \033[34m<==\033[0m ", file=sys.stderr)

def print_success(msg: str):
    print("[\033[32m+\033[0m] " +  msg, file=sys.stderr)

def print_fail(msg: str):
    print("[\033[31mX\033[0m] " +  msg, file=sys.stderr)

def flatten_dict(list_of_dicts: list[dict] ) -> dict:
    flat = {}
    for di in list_of_dicts:
        for key,val in di.items():
            if not key in flat:
                flat[key] = []
            flat[key].extend(val)

    return flat

def flatten_set(list_of_sets: list[Set]) -> Set:
    flat = set()
    for li in list_of_sets:
        for item in li:
            flat.add(item)
    return flat

def flatten(list_of_lists: list[list]) -> list:
    flat = []
    for li in list_of_lists:
        flat.extend(li)
    return flat

def get_column_counts(blob: str, column_index:int, sep:str = "") -> list[tuple[str,int]]:
    ''' 
    Return the number of occurences of each string in a newline seperated file
    for a given seperator and column index (zero based). Empty on failure
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
        if column_value in column_stats.keys():
            column_stats[column_value] += 1
        else:
            column_stats[column_value] = 1

    return list(column_stats.items())

def unique_only(li: list) -> list:
    uniq = []
    for item in li:
        if not item in uniq:
            uniq.append(item)
    return uniq

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
        case AnalysisResult.FAILURE:
            print_fail(msg)
        case AnalysisResult.NO_VCCS:
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

def time_end(msg: str, start_time: datetime, result: AnalysisResult = AnalysisResult.NONE) -> None:
    if CONFIG.VERBOSITY >= 1:
        print_result(f"{msg}: {datetime.now() - start_time}", result)
        start_time = datetime.now()

def mkdir_p(path: str):
    if not os.path.exists(path):
        os.mkdir(path)

def rm_f(path: str):
    if os.path.exists(path):
        os.remove(path)

def has_allowed_suffix(string) -> bool:
    suffixes = "|".join(CONFIG.SUFFIX_WHITELIST).strip("|").replace(".", "\\.")
    return re.match(rf".*({suffixes})$", string) != None

def remove_files_in(path: str):
    if os.path.isdir(path):
        for file in os.listdir(path):
            filepath = f"{path}/{file}"
            if os.path.isfile(filepath):
                os.remove(filepath)
