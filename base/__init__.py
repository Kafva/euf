from dataclasses import dataclass
from clang import cindex

NPROC = 5

cindex.Config.set_library_file("/usr/lib/libclang.so.13.0.1")

@dataclass(init=True)
class Function:
    filepath: str
    displayname: str # Includes the full prototype string
    name: str
    return_type: cindex.TypeKind
    arguments: list[ tuple[cindex.TypeKind,str] ]

    def __repr__(self):
        return f"{self.filepath}:{self.name}"

@dataclass(init=True)
class Invocation:
    function: Function
    filepath: str
    #trace: str # Call-trace in the main project to reach the invocation
    location: cindex.SourceLocation

    def __repr__(self):
        return f"{self.filepath}"

@dataclass(init=True)
class CursorPair:
    new: cindex.Cursor | None
    old: cindex.Cursor | None

    def __init__(self):
        self.new = None
        self.old = None

    def add(self, cursor: cindex.Cursor, is_new: bool):
        if is_new:
            self.new = cursor
        else:
            self.old = cursor

def flatten(list_of_list: list[list]) -> list:
    flat = []
    for li in list_of_list:
        flat.extend(li)
    return flat


