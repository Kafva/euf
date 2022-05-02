from src.config import CONFIG
from src.types import CallSite, DependencyFunction, \
    DependencyFunctionChange, IdentifierLocation
from src.util import git_relative_path

def fmt_location(ident: IdentifierLocation) -> str:
    path = git_relative_path(ident.filepath)

    if ident.name != "":
        return f"{path}:{ident.line}:{ident.column}:{ident.name}"
    else:
        return f"{path}:{ident.line}:{ident.column}"

def fmt_change(change: DependencyFunctionChange, pretty: bool = False,
 brief: bool = False) -> str:
    out = ""
    if pretty:
        out =   "\033[31mDirect\033[0m change: " if change.direct_change else \
                "\033[34mIndirect\033[0m change: "
    else:
        out =   "direct change: " if change.direct_change else \
                "indirect change: "
    if brief and pretty:
            out += "\033[33m"

    old_func = fmt_location(change.old.ident.location)
    new_func = fmt_location(change.new.ident.location)

    if change.old.ident.location.name == "":
        out += f"b/{new_func}()"
    else:
        out += f"a/{old_func}() -> b/{new_func}()"
    if brief and pretty:
            out += "\033[0m"

    if not brief:
        out += affected_by(change,pretty)

    return out

def affected_by(change: DependencyFunctionChange, pretty=True) -> str:
    out = ""
    if len(change.invokes_changed_functions) > 0:
        if pretty:
            out += "\nAffected by changes to:"
        else:
            out += "\naffected by changes to:"

        for trans_call in change.invokes_changed_functions:
            out += f"\n{CONFIG.INDENT}{git_relative_path(trans_call)}"
    return out

def fmt_call_site(call_site: CallSite, pretty: bool = False,
 brief: bool = False) -> str:
    change_str = fmt_change(call_site.called_function_change, pretty, brief)
    location_str = fmt_location(call_site.call_location)
    return f"call to {change_str} at {location_str}()"

def fmt_divergence(change: DependencyFunctionChange,
 with_context:bool=True) -> str:
    divergence = fmt_location(change.point_of_divergence)
    if with_context:
        return f"{fmt_change(change)}\n{CONFIG.INDENT}diverged at \033[4m{divergence}\033[0m"
    else:
        return f"\n{CONFIG.INDENT}diverged at \033[4m{divergence}\033[0m"

def print_changes(changed_functions: list[DependencyFunctionChange],
 pretty:bool = False, brief:bool = False) -> None:
    out = ""
    for change in changed_functions:
        out += fmt_change(change, pretty, brief) + "\n"
    print(out.rstrip('\n'), flush=True)

def print_transistive_changes(func_dict: dict[DependencyFunction,list[str]]):
    out = ""
    for func in func_dict.keys():
        # Indirectly changed function
        out += fmt_location(func.ident.location)

        # List of calls to changed functions 
        out += ": [\n"
        for call in set(func_dict[func]):
            out += f"{CONFIG.INDENT}{git_relative_path(call)},\n"
        out.rstrip(",")
        out += "]\n"
    print(out)

def print_call_sites(call_sites: list[CallSite],
 pretty:bool = False, brief: bool = False):
    out = ""
    for call in call_sites:
        out += fmt_call_site(call, pretty, brief) + "\n\n"
    print(out.rstrip('\n'))

