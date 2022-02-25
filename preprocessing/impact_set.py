from clang import cindex
from base import DependencyFunction, ProjectInvocation, SourceFile

def get_call_sites_from_file(source_file: SourceFile,
    changed_functions: list[DependencyFunction]) -> list[ProjectInvocation]:
    '''
    Return a list of call sites in the provided source
    file for the functions in `changed_functions`
    '''
    call_sites = []

    translation_unit: cindex.TranslationUnit  = cindex.TranslationUnit.from_source(
            source_file.new_path, args = source_file.compile_args
    )
    cursor: cindex.Cursor       = translation_unit.cursor

    find_call_sites_in_tu(source_file.new_path, cursor, changed_functions, call_sites)

    return call_sites


def find_call_sites_in_tu(filepath: str, cursor: cindex.Cursor,
    changed_functions: list[DependencyFunction], call_sites: list[ProjectInvocation]) -> None:
    '''
    Go through the complete AST of the provided file and save any sites
    where a changed function is called as an invocation
    '''
    if str(cursor.kind).endswith("CALL_EXPR") and \
            (dep_func := next(filter(lambda fn: \
            fn.name == cursor.spelling, changed_functions), None \
    )):

        # We haft to verify that the called function has the expected parameters,
        # since there could be a local function with the same name
        # TODO: identify if our version of the function is included in the main file being analyzed
        # otherwise the error could be a FP
        matching_args = True

        func_args_main_types = [ str(child.type.kind) for child in cursor.get_arguments() ]

        if len(func_args_main_types) != len(dep_func.arguments):
            matching_args = False
        else:
            for fn_arg_dep, fn_arg_main_type in zip(dep_func.arguments, func_args_main_types):

                if fn_arg_dep.type != fn_arg_main_type:
                    matching_args = False
                    break

        invocation = ProjectInvocation(
                function = dep_func,
                filepath = filepath,
                line = cursor.location.line,
                col  = cursor.location.column
        )

        if matching_args:
            call_sites.append(invocation)
        else:
            print(f"\033[31m=>\033[0m Potentially inconsistent parameters for {invocation}:" +
                    f"\n  Prototype: {dep_func.displayname}\n  Invocation: {cursor.spelling}(" +
                    f", ".join(func_args_main_types) + ")"
            )
    else:
        # We do not need to process children of a remote call
        for child in cursor.get_children():
            find_call_sites_in_tu(filepath, child, changed_functions, call_sites)
