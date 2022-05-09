#!/usr/bin/env python3
import os,sys
import matplotlib.pyplot as plt
from posixpath import expanduser

# '.' is needed to run from the visualise directory
sys.path.extend(['..','.'])

from visualise import OPTIONS
from visualise.plot import plot_analysis_dists, plot_reductions
from visualise.case import Case
from src.config import CONFIG
from src.types import AnalysisResult
from src.util import print_info, print_stage

def write_report(cases: list[Case], only_multi:bool=False):
    '''
    Make a MD template for the correctness analysis
    For each function the template gives a command to test the harness
    and a command to view the diff of the file wherein the function
    being tested resides

    ./scripts/analyze_function.sh onig unset_addr_list_fix f30e 158e
    git difftool --no-index ~/.cache/euf/oniguruma-f30edcce/src/regcomp.c
                        ~/.cache/euf/oniguruma-158e/src/regcomp.c
    # => /home/jonas/.cache/euf/oniguruma-f30edcce/.harnesses/unset_addr_list_fix.c (SUCCESS_UNWIND_FAIL)

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
                    overlap = set(func_result.results) & {AnalysisResult.SUCCESS,
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
                        if r.func_name == func_result.func_name and not r.identity:

                            # The exact file that has the change can be determined from
                            # change_set.csv
                            trial_path = \
                                f"{CONFIG.RESULTS_DIR}/{case.libname()}_" \
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
                                euf_cache_dir_old.replace(expanduser('~'),"~")
                            euf_cache_dir_new = \
                                euf_cache_dir_new.replace(expanduser('~'),"~")

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
                            f.write(f"# => {driver} ({r.result.name})\n")
                    f.write("```\n")
                    f.write("\n\n")

def save_figure(path: str):
    if os.path.isdir(os.path.dirname(path)) and OPTIONS['SAVE_FIGS']:
        plt.savefig(path, dpi=900)

def dir_cnt(path:str):
    return len([ p for p in os.listdir(path) \
            if os.path.isdir(f"{path}/{p}")])

def load_cases(result_dir:str, result_dir_impact:str) -> list[Case]:
    CONFIG.RESULTS_DIR = result_dir
    onig = Case.new(name="libonig", result_dir=CONFIG.RESULTS_DIR,
            total_functions=1186, color=OPTIONS['RED'])
    onig.load_change_sets()
    onig.load_impact_set()

    expat = Case.new(name="libexpat", result_dir=CONFIG.RESULTS_DIR,
            total_functions=645, color='#32a852')
    expat.load_change_sets()
    expat.load_impact_set()

    usb = Case.new(name="libusb", result_dir=CONFIG.RESULTS_DIR,
            total_functions=1346, color=OPTIONS['BLUE'])
    usb.load_change_sets()
    usb.load_impact_set()

    CONFIG.RESULTS_DIR = result_dir_impact
    onig.load_change_sets(without_reduction=True)
    onig.load_impact_set(without_reduction=True)

    expat.load_change_sets(without_reduction=True)
    expat.load_impact_set(without_reduction=True)

    usb.load_change_sets(without_reduction=True)
    usb.load_impact_set(without_reduction=True)

    return [onig,expat,usb]

if __name__ == '__main__':
    plt.style.use('dark_background')

    total_trials = dir_cnt(OPTIONS['RESULT_DIR'])
    print_info(f"Total trials: {total_trials} ({round(total_trials/3,1)} per project)")

    cases = load_cases(OPTIONS['RESULT_DIR'], OPTIONS['IMPACT_DIR'])

    CONFIG.RESULTS_DIR = OPTIONS['RESULT_DIR']

    if OPTIONS['PLOT']:
        plot_analysis_dists(cases,ident=True)
        save_figure(f"{OPTIONS['FIGURE_DIR']}/result_dist_id.png")
        plot_analysis_dists(cases,ident=False)
        save_figure(f"{OPTIONS['FIGURE_DIR']}/result_dist.png")
        plot_reductions(cases,percent=False)
        save_figure(f"{OPTIONS['FIGURE_DIR']}/reduction_violin.png")

        plt.subplots_adjust(bottom=0.15)
        plt.xticks(fontsize=OPTIONS['PLOT_FONT_SIZE'])
        plt.show()

    # Specify what we consider as a 'multi-result'
    CONFIG.REDUCE_INCOMPLETE_UNWIND = True
    print_info(f"REDUCE_INCOMPLETE_UNWIND: "
        f"{CONFIG.REDUCE_INCOMPLETE_UNWIND}\n"
    )
    for c in cases:
        c.info(OPTIONS['UNIQUE_RESULTS'])

    if OPTIONS['WRITE_MD']:
        write_report(cases,only_multi=OPTIONS['ONLY_MULTI'])
    if OPTIONS['LIST_ANALYZED']:
        print("\n=============================")
        for case in cases:
            print_stage(case.name)
            results = case.multi_result_function_results() \
                    if OPTIONS['ONLY_MULTI'] \
                    else case.fully_analyzed_functions()
            for r in results:
                print(r.pretty())
