from typing import Set
from clang import cindex
from cparser import CONFIG, DependencyFunctionChange, \
        ProjectInvocation, SourceFile
from cparser.util import print_err

def get_call_sites_from_file(source_file: SourceFile,
    changed_functions: Set[DependencyFunctionChange]
    ) -> list[ProjectInvocation]:
    '''
    Return a list of call sites (to the old version of functions) in the 
    provided source file for the functions in `changed_functions`
    '''
    call_sites = []

    translation_unit: cindex.TranslationUnit  = \
        cindex.TranslationUnit.from_source(
            source_file.new_path, args = source_file.new_compile_args
    )
    cursor: cindex.Cursor       = translation_unit.cursor
    current_enclosing = ""

    find_call_sites_in_tu(source_file.new_path, cursor,
        changed_functions, call_sites, current_enclosing
    )

    return call_sites

def find_call_sites_in_tu(filepath: str, cursor: cindex.Cursor,
    changed_functions: Set[DependencyFunctionChange],
    call_sites: list[ProjectInvocation], current_enclosing: str) -> None:
    '''
    Go through the complete AST of the provided file and save any sites
    where a changed function is called as an invocation
    '''
    if str(cursor.kind).endswith("FUNCTION_DECL") and cursor.is_definition():
        # Keep track of the current enclosing function
        current_enclosing = cursor.spelling

    if str(cursor.kind).endswith("CALL_EXPR") and \
        (dep_func_change := next(filter(lambda fn: \
        fn.old.name == cursor.spelling, changed_functions), None \
    )):

        # Look for conflicts in types of parameters that are passed
        # in the main project to the new version of each changed function
        matching_args = True

        func_args_main_types = [ str(child.type.kind) \
                for child in cursor.get_arguments() ]

        if len(func_args_main_types) != len(dep_func_change.new.arguments):
            matching_args = False
        else:
            for fn_arg_dep, fn_arg_main_type in \
                    zip(dep_func_change.new.arguments, func_args_main_types):

                if fn_arg_dep.type != fn_arg_main_type:
                    matching_args = False
                    break

        invocation = ProjectInvocation(
                function = dep_func_change,
                enclosing_name = current_enclosing,
                filepath = filepath,
                line = cursor.location.line,
                col  = cursor.location.column
        )

        call_sites.append(invocation)

        if not matching_args and CONFIG.VERBOSITY >= 1:
            print_err(f"Potentially inconsistent parameters in {invocation.brief()}:" +
            f"\n  New prototype: {dep_func_change.new.name}(" + \
            ", ".join(map(lambda a: a.type, dep_func_change.new.arguments))+ ")"
            f"\n  Invocation: {cursor.spelling}(" +
            ", ".join(func_args_main_types) + ")"
            )
    for child in cursor.get_children():
        find_call_sites_in_tu(filepath, child, changed_functions, call_sites,
            current_enclosing
        )

def pretty_print_impact(call_sites: list[ProjectInvocation]) -> None:
    '''
    Group the call sites by the file and enclosing function that
    they belong to.
    '''
    location_to_calls_dict = dict()

    for site in call_sites:
        key = f"{site.filepath}:{site.enclosing_name}()"

        if key in location_to_calls_dict:
            location_to_calls_dict[key].add(
                site.function.detail(pretty=True)
            )
        else:
            location_to_calls_dict[key] = set(
                { site.function.detail(pretty=True) }
            )

    for location,calls in location_to_calls_dict.items():
        print(f"=== \033[33m{location}\033[0m ===")
        for call in calls:
            print(call)