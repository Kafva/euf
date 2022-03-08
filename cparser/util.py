import sys, re
from typing import Set

from git.repo.base import Repo

from cparser import CONFIG

def print_info(msg: str):
    print("\033[34m!>\033[0m " +  msg, file=sys.stderr)

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

def top_stash_is_euf_internal(repo: Repo) -> bool:
    top_stash: str = repo.git.stash("list").split('\n', 1)[0] # type: ignore
    return top_stash.endswith(CONFIG.CACHE_INTERNAL_STASH)

def remove_prefix(target: str, prefix: str) -> str:
    if target.startswith(prefix):
        return target[len(prefix):]
    else:
        return target
