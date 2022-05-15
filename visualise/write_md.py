import os
from posixpath import expanduser

from src.config import CONFIG
from src.types import AnalysisResult, HarnessType
from visualise.case import Case

def write_md(cases: list[Case], result_dir:str, only_multi:bool=False):
    '''
    Make a MD template for the correctness analysis
    For each function the template gives a command to test the harness
    and a command to view the diff of the file wherein the function
    being tested resides

    ./scripts/analyze_function.sh onig unset_addr_list_fix f30e 158e
    git difftool --no-index ~/.cache/euf/oniguruma-f30edcce/src/regcomp.c
                        ~/.cache/euf/oniguruma-158e/src/regcomp.c
    # => /home/jonas/.cache/euf/oniguruma-f30edcce/.harnesses/unset_addr_list_fix.c 
    # (SUCCESS_UNWIND_FAIL)

    The only_multi option will limit the report to functions where both a FAILED
    and SUCCESS result were attained.
    '''
    with open("correctness.md", mode = 'w', encoding='utf8') as f:
        for case in cases:
            results = case.multi_result_function_results() if only_multi \
                    else case.function_results()
            f.write(f"# {case.name}\n")

            for func_result in results:
                if not only_multi:
                    overlap = set(func_result.results()) & {AnalysisResult.SUCCESS,
                       AnalysisResult.SUCCESS_UNWIND_FAIL,
                       AnalysisResult.SUCCESS_UNWIND_FAIL,
                       AnalysisResult.FAILURE}
                    should_write = len(overlap) > 0
                else: # Only iterating over valid results already
                    should_write = True

                if should_write:
                    f.write(func_result.pretty_md())

                    # Find all commits where a CBMC result
                    # was present for the current function
                    # and print an analysis command for each one
                    f.write("```bash\n")
                    for r in case.cbmc_results():
                        if r.func_name == func_result.func_name and \
                            r.harness_type == HarnessType.STANDARD:

                            # The exact file that has the change can be determined from
                            # change_set.csv
                            trial_path = \
                                f"{result_dir}/{case.libname()}_" \
                                f"{r.commit_old}_{r.commit_new}"

                            change_set = case.base_change_set[trial_path]

                            function_change = next( c for c in change_set if
                                    c.old.ident.location.name == r.func_name )

                            # These directories (with 4 characters of the commit
                            # hash in their name) will only be available
                            # after running `analyze_function.sh`
                            euf_cache_dir_old = \
                                f"{CONFIG.EUF_CACHE}/{case.reponame()}-{r.commit_old}"
                            euf_cache_dir_new = \
                                f"{CONFIG.EUF_CACHE}/{case.reponame()}-{r.commit_new}"

                            euf_cache_dir_old = \
                                euf_cache_dir_old.replace(expanduser('~'),'~')
                            euf_cache_dir_new = \
                                euf_cache_dir_new.replace(expanduser('~'),'~')

                            f.write(f"./scripts/analyze_function.sh "
                                f"{case.name.removeprefix('lib')} "
                                f"{r.func_name} "
                                f"{r.commit_old} {r.commit_new}\n"
                            )
                            f.write("git difftool --no-index "
                                    f"{euf_cache_dir_old}/"
                                    f"{function_change.old.ident.location.filepath} "
                                    f"{euf_cache_dir_new}/"
                                    f"{function_change.new.ident.location.filepath}\n"
                            )
                            f.write(f"# {function_change.old.ident.location.line}"
                                    f":{function_change.old.ident.location.column}"
                                    f" <-> {function_change.new.ident.location.line}"
                                    f":{function_change.new.ident.location.column}\n"
                            )
                            driver = f"{euf_cache_dir_old}/.harnesses/"+\
                                os.path.basename(r.driver)
                            f.write(f"# => {driver} ({next(iter(r.result)).name})\n")
                    f.write("```\n")
                    f.write("\n\n")

