import dataclasses
import json
import traceback
from typing import Set
from clang import cindex
from cparser import CONFIG, DependencyFunction, DependencyFunctionChange, \
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

    try:
        translation_unit: cindex.TranslationUnit  = \
            cindex.TranslationUnit.from_source(
                source_file.new_path, args = source_file.new_compile_args
        )
        cursor: cindex.Cursor       = translation_unit.cursor
        current_enclosing = ""

        find_call_sites_in_tu(source_file.new_path, cursor,
            changed_functions, call_sites, current_enclosing
        )
    except cindex.TranslationUnitLoadError:
        traceback.print_exc()
        print_err(f"Failed to create TU for {source_file.new_path}")

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
        (dep_func := next(filter(lambda fn: \
        fn.new.ident.spelling == cursor.spelling, changed_functions), None \
    )):
        # Ensure that return type and arguments of the call
        # match the prototype in the change set
        called = DependencyFunction.new_from_cursor(CONFIG.PROJECT_DIR, cursor)

        if dep_func.new.eq(called):
            invocation = ProjectInvocation(
                    function = dep_func,
                    enclosing_name = current_enclosing,
                    filepath = filepath,
                    line = cursor.location.line,
                    col  = cursor.location.column
            )
            call_sites.append(invocation)

    for child in cursor.get_children():
        find_call_sites_in_tu(filepath, child, changed_functions, call_sites,
            current_enclosing
        )

def log_impact_set(call_sites: list[ProjectInvocation], filename: str) -> None:
    '''
    A full record of the impact set will 
    be recoreded as a JSON dump of the ProjectInvocation list

    We would not benefit from making two different CSV logging schemes (with reversed mappings)
    since every line would still need an impact site and a change site
    '''
    if CONFIG.ENABLE_RESULT_LOG:
        with open(filename, mode='w', encoding='utf8') as f:
            # Each ProjectInvocation only contains one DependencyFunctionChange object
            # so we can log the source of the change with the impact site
            # What functions cause an indirect change is not recorded in the CSV format
            f.write("impact_site;impacted_func;line;col;change_src;changed_func;line;col\n")
            for invocation in call_sites:
                f.write(f"{invocation.to_csv()}\n")

        with open(f"{filename.removesuffix('.csv')}.json", mode='w', encoding='utf8') as f:
            json.dump([ dataclasses.asdict(c) for c in call_sites ], f)

def pretty_print_impact_by_proj(call_sites: list[ProjectInvocation]) -> None:
    '''
    Print each impact site as its own header with a list of dependency change
    sources beneath it
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
        print("Changed function calls:\n")
        for call in calls:
            print(call)

def pretty_print_impact_by_dep(call_sites: list[ProjectInvocation]) -> None:
    '''
    Print each dependency change as its own header with a list of impact sites 
    in our project beneath it
    '''

    # Create a dictonary that maps a DependencyFunctionChange to a list of
    # affected call sites in our project
    func_change_to_invocations_map = {}

    # Each function change can contain a list of changed functions that they
    # call (making them indirectly changed functions) or be directly changed

    for site in call_sites:
        if site.function in func_change_to_invocations_map.keys():
            func_change_to_invocations_map[site.function].append(site)
        else:
            func_change_to_invocations_map[site.function] = [ site ]


    for dep_change,affected in func_change_to_invocations_map.items():
        print(f"=== \033[33m{dep_change.detail(pretty=True,brief=True)}\033[0m ===")

        print("Called from:")
        for site in affected:
            print("\t"+site.invocation())

        print(dep_change.affected_by(pretty=True))

