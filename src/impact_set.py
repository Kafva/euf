import dataclasses
import json
import traceback
from typing import Set
from clang import cindex
from src.config import CONFIG
from src.types import DependencyFunction, DependencyFunctionChange, \
        CallSite, IdentifierLocation, SourceFile
from src.util import print_err

def get_call_sites_from_file(source_file: SourceFile,
        changed_functions: Set[DependencyFunctionChange]
    ) -> list[CallSite]:
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
    call_sites: list[CallSite], current_enclosing: str) -> None:
    '''
    Go through the complete AST of the provided file and save any sites
    where a changed function is called as an call_site
    '''
    if str(cursor.kind).endswith("FUNCTION_DECL") and cursor.is_definition():
        # Keep track of the current enclosing function
        current_enclosing = cursor.spelling

    if str(cursor.kind).endswith("CALL_EXPR") and \
        (changed_function := next(filter(lambda fn: \
        fn.new.ident.spelling == cursor.spelling, changed_functions), None \
    )):
        # Ensure that return type and arguments of the call
        # match the prototype in the change set
        called = DependencyFunction.new_from_cursor(CONFIG.PROJECT_DIR, cursor)

        if changed_function.new.eq(called):
            call_site = CallSite(
                    called_function_change = changed_function,
                    call_location = IdentifierLocation(
                        filepath = str(cursor.location.file),
                        line = cursor.location.line,
                        column = cursor.location.column,
                        name = current_enclosing
                    )
            )
            call_sites.append(call_site)

    for child in cursor.get_children():
        find_call_sites_in_tu(filepath, child, changed_functions, call_sites,
            current_enclosing
        )

def log_impact_set(call_sites: list[CallSite], filename: str) -> None:
    '''
    A full record of the impact set will 
    be recorded as a JSON dump of the CallSite list

    We would not benefit from making two different CSV logging schemes (with reversed mappings)
    since every line would still need an impact site and a change site
    '''
    if CONFIG.ENABLE_RESULT_LOG:
        with open(filename, mode='w', encoding='utf8') as f:
            # Each CallSite only contains one DependencyFunctionChange object
            # so we can log the source of the change with the impact site
            # What functions cause an indirect change is not recorded in the CSV format
            f.write(f"{CallSite.csv_header()}\n")
            sorted_by_type = sorted(call_sites, key = lambda c:
                    c.called_function_change.direct_change,
                    reverse=True
            )
            for call_site in sorted_by_type:
                f.write(f"{call_site.to_csv()}\n")

        with open(f"{filename.removesuffix('.csv')}.json", mode='w', encoding='utf8') as f:
            json.dump([ dataclasses.asdict(c) for c in call_sites ], f)

def pretty_print_impact_by_call_site(call_sites: list[CallSite]) -> None:
    '''
    Print each impact site as its own header with a list of dependency change
    sources beneath it

    Note: a "site" object consists of one call to a dependency function from the 
    main project, i.e. there can be several site objects that have the same
    enclosing function.
    '''
    location_to_calls_dict: dict[str,set[str]] = dict()

    for site in call_sites:
        # To compile all calls within the same enclosing function
        # together we only use the filepath and name as keys
        # since the line and column will differ
        key = f"{site.call_location.filepath}:{site.call_location.name}()"
        called_at = f"({site.call_location.line}:{site.call_location.column}) "
        out_str = called_at + site.called_function_change.__repr__(pretty=True)

        # Show the point of divergence for direct changes
        if site.called_function_change.direct_change:
           out_str += f"{CONFIG.INDENT}" + \
                    site.called_function_change.divergence(with_context=False)

        if key in location_to_calls_dict:
            location_to_calls_dict[key].add(out_str)
        else:
            location_to_calls_dict[key] = set({out_str})

    for location,calls in location_to_calls_dict.items():
        print(f"\n=== \033[33m{location}\033[0m ===")
        print("Changed function calls:\n")
        for call in calls:
            print(call)

def pretty_print_impact_by_dep(call_sites: list[CallSite]) -> None:
    '''
    Print each dependency change as its own header with a list of impact sites 
    in our project beneath it
    '''

    # Create a dictionary that maps a DependencyFunctionChange to a list of
    # affected call sites in our project
    func_change_to_invocations_map = {}

    # Each function change can contain a list of changed functions that they
    # call (making them indirectly changed functions) or be directly changed

    for site in call_sites:
        key = site.called_function_change
        if key in func_change_to_invocations_map.keys():
            func_change_to_invocations_map[key].append(site)
        else:
            func_change_to_invocations_map[key] = [ site ]


    for dep_change,affected in func_change_to_invocations_map.items():
        print(f"\n=== \033[33m{dep_change.__repr__(pretty=True, brief=True)}\033[0m ===")

        affected_str = dep_change.affected_by(pretty=True)
        if affected_str!="":
            print(affected_str.lstrip('\n')+"\n")

        print("Called from:")
        for site in affected:
            print(f"{CONFIG.INDENT}{site.call_location}()")

