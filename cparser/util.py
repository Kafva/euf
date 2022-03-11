import sys
from typing import Set

def print_info(msg: str):
    print("\033[34m!>\033[0m " +  msg, file=sys.stderr)

def print_stage(msg: str):
    print("\033[34m==>\033[0m " +  msg + " \033[34m<==\033[0m ", file=sys.stderr)

def print_err(msg: str):
    print("\033[31m!>\033[0m " +  msg, file=sys.stderr)

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

def remove_prefix(target: str, prefix: str) -> str:
    if target.startswith(prefix):
        return target[len(prefix):]
    else:
        return target

def get_path_relative_to(path: str, base: str) -> str:
    return remove_prefix( remove_prefix(path, base), "/")

def unique_only(li: list) -> list:
    uniq = []
    for item in li:
        if not item in uniq:
            uniq.append(item)
    return uniq
