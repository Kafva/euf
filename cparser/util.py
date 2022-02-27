from typing import Set

def print_err(msg: str):
    print("\033[31m!>\033[0m " +  msg)

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

