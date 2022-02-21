from enum import Enum
from dataclasses import dataclass
from clang import cindex

cindex.Config.set_library_file("/usr/lib/libclang.so.13.0.1")

@dataclass(init=True)
class Function:
    filepath: str
    displayname: str # Includes the full prototype string
    name: str
    return_type: cindex.TypeKind
    arguments: list[ tuple[cindex.TypeKind,str] ]

@dataclass(init=True)
class Invocation:
    function: Function
    filepath: str
    # Call-trace in the main project to reach the invocation
    trace: str
    #row_nr: int
    #col_nr: int

class CursorContext(Enum):
    CURRENT = "old"
    NEW = "new"

def debug_print(fmt: str, hl:bool = False) -> None:
    if DEBUG:
        if hl: print("\033[34m=>\033[0m ", end='')
        print(fmt)


def flatten(list_of_list: list[list]) -> list:
    flat = []
    for li in list_of_list:
        flat.extend(li)
    return flat

DEBUG = False
NPROC = 5

