from enum import Enum
from dataclasses import dataclass
from clang import cindex

cindex.Config.set_library_file("/usr/lib/libclang.so.13.0.1")

@dataclass
class Function:
    displayname: str # Includes the full prototype string
    name: str
    return_type: cindex.TypeKind
    arguments: list[ tuple[cindex.TypeKind,str] ]

class CursorContext(Enum):
    CURRENT = "old"
    NEW = "new"

def debug_print(fmt: str, hl:bool = False) -> None:
    if DEBUG:
        if hl: print("\033[34m=>\033[0m ", end='')
        print(fmt)

DEBUG = False
NPROC = 5

