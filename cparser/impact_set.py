from typing import Set
from clang import cindex
from cparser import DependencyFunctionChange, ProjectInvocation, SourceFile
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

    find_call_sites_in_tu(source_file.new_path, cursor,
        changed_functions, call_sites
    )

    return call_sites

def find_call_sites_in_tu(filepath: str, cursor: cindex.Cursor,
    changed_functions: Set[DependencyFunctionChange],
    call_sites: list[ProjectInvocation]) -> None:
    '''
    Go through the complete AST of the provided file and save any sites
    where a changed function is called as an invocation
    '''
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
                filepath = filepath,
                line = cursor.location.line,
                col  = cursor.location.column
        )

        call_sites.append(invocation)

        if not matching_args:
            print_err(f"Potentially inconsistent parameters in {invocation}:" +
            f"\n  New prototype: {dep_func_change.new.name}(" + \
            ", ".join(map(lambda a: a.type, dep_func_change.new.arguments))+ ")"
            f"\n  Invocation: {cursor.spelling}(" +
            ", ".join(func_args_main_types) + ")"
            )
    else:
        # We do not need to process children of a remote call
        for child in cursor.get_children():
            find_call_sites_in_tu(filepath, child, changed_functions, call_sites)
