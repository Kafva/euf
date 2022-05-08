#!/usr/bin/env python3
'''
  Correctness
  ============
  * Run X random cases for each project

  * Grep out the subset of equivalent (`SUCCESS`) (TN|FN) cases, 
    there should be a major overlap in what functions appear

  * Grep out the subset of influential (`FAILURE`) (TP|FP) cases, 
    there should be a major overlap in what functions appear

  * Interrogate each function individually to determine if the result is trustworthy
    - Record in a CSV:
       - function_name;dependency;results;trusted
    - "results" should hold all recorded results for this function
    - "trusted" should be set as True, True(unwind) False or Inconclusive
    - "description" should motivate the trusted column"s value (separate
      markdown doc, with pictures)

  * With some form of correctness assessment for each function, we can show a
    plot of what percentage of the analysis could be considered reliable
    (CSV entries for functions that are not reliable -> False else True)

  Plots
  ======
    * Reduction in change and impact set (mean,lowest,highest graph)
    
'''

from posixpath import expanduser
import sys,os
import matplotlib.pyplot as plt
from itertools import compress
from textwrap import wrap

# '.' is needed to run from the visualise directory 
sys.path.extend(['..','.'])

from visualise.types import Case
from src.config import CONFIG
from src.types import AnalysisResult

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

def plot_analysis_dists(cases:
        list[Case],ident:bool=False,unique_results:bool=False):
    '''
    Not using the `unique_results` option gives the impression that expat has
    very good performance, which stems from the fact that it has analyzed
    the same few functions successfully many times.
    '''
    cases_dists = [ c.analysis_dist(
                        ident=ident,
                        unique_results=unique_results
                    ).values() for c in cases ]

    non_zero_fields = [ a!=0 or b!=0 or c!=0 for a,b,c in
            zip(cases_dists[0],
                cases_dists[1],
                cases_dists[2]) ]

    # Remove fields that are zero across all cases
    cases_dists = [ list(compress(c,non_zero_fields)) for c in cases_dists ]

    bar_names = [ e.name for e in AnalysisResult ]
    bar_names  = list(compress(bar_names, non_zero_fields))

    # Wrap the bar name text to X chars
    bar_names = [ '\n'.join(wrap(l, OPTIONS['PLOT_WRAP_CHARS'])) for l in bar_names ]

    _, axes = plt.subplots()

    # Color-code a bar plot for each case
    for i,case in enumerate(cases):
        # The bottom value must be correctly set to the sum of the previous 
        # bars, otherwise overlaps will occur
        match i:
            case 1: bottom = cases_dists[0]
            case 2: bottom = [ x+y for x,y in zip(cases_dists[0],cases_dists[1]) ]
            case _: bottom = 0

        axes.bar(bar_names, cases_dists[i],
                OPTIONS['PLOT_WIDTH'],
                label=case.name,
                color=[ cases[i].color ],
                bottom = bottom,
                edgecolor='white'
        )

    axes.set_ylabel('')
    axes.set_title(f"Distribution of CBMC {'identity ' if ident else ''}analysis "
            "results " +\
            ("(without duplicates)" if unique_results else "(with duplicates)"),
            fontweight='bold', fontsize=12

    )

    axes.legend(loc='upper left')

def plot_reductions(cases: list[Case]):
    '''
    We want to show the average reduction, stdev from the average and the
    extreme values, a violin plot is suitable for this
    '''

    change_set_reductions = [ c.change_set_reductions_per_trial() for c in cases ]
    trans_set_reductions =  [ c.trans_set_reductions_per_trial() for c in cases ]
    impact_set_reductions = [ c.impact_set_reductions_per_trial() for c in cases ]

    fig = plt.figure()
    subfigs = fig.subfigures(nrows=3, ncols=1)

    def create_row(title,index,array,label):
        subfigs[index].suptitle(title,fontweight='bold',
                horizontalalignment='center'
        )
        axes = subfigs[index].subplots(nrows=1, ncols=3)
        axes[0].set_ylabel(f"Items removed from {label} set [#]")

        for i, ax in enumerate(axes):
            ax.violinplot(
                array[i],
                showmeans=True, showextrema=True
            )
            if index==2:
                ax.set_xlabel(cases[i].name,
                        fontweight='normal',
                        fontsize=12,
                        horizontalalignment='center',
                )

    create_row("Base change set reduction", 0, change_set_reductions, "change")
    create_row("Transitive change set reduction", 1, trans_set_reductions,
            "transitive")
    create_row("Impact set reduction", 2, impact_set_reductions, "impact")

OPTIONS = {
    'PLOT_WIDTH': 0.35,
    'PLOT_FONT_SIZE': 10,
    'PLOT_WRAP_CHARS': 10,
    'WRITE_MD': True,
    'PLOT': False,
    'LIST_ANALYZED': True,
    'UNIQUE_RESULTS': False,
    'RESULT_DIR': ".results/6",
    'IMPACT_DIR': ".results/6_impact",
    'ONLY_MULTI': True
}

if __name__ == '__main__':
    plt.style.use('dark_background')

    CONFIG.RESULTS_DIR = OPTIONS['RESULT_DIR']
    onig = Case.new(name="libonig", total_functions=1186, color='#d44848')
    onig.load_change_sets()
    onig.load_impact_set()

    expat = Case.new(name="libexpat", total_functions=645, color='#32a852')
    expat.load_change_sets()
    expat.load_impact_set()

    usb = Case.new(name="libusb", total_functions=1346, color='#467fdb')
    usb.load_change_sets()
    usb.load_impact_set()

    CONFIG.RESULTS_DIR = OPTIONS['IMPACT_DIR']
    onig.load_change_sets(without_reduction=True)
    onig.load_impact_set(without_reduction=True)

    expat.load_change_sets(without_reduction=True)
    expat.load_impact_set(without_reduction=True)

    usb.load_change_sets(without_reduction=True)
    usb.load_impact_set(without_reduction=True)

    CONFIG.RESULTS_DIR = OPTIONS['RESULT_DIR']

    onig.info(OPTIONS['UNIQUE_RESULTS'])
    expat.info(OPTIONS['UNIQUE_RESULTS'])
    usb.info(OPTIONS['UNIQUE_RESULTS'])

    cases = [onig,expat,usb]

    if OPTIONS['PLOT']:
        plot_analysis_dists(cases,ident=True,unique_results=OPTIONS['UNIQUE_RESULTS'])
        plot_analysis_dists(cases,ident=False,unique_results=OPTIONS['UNIQUE_RESULTS'])
        plot_reductions(cases)

        plt.xticks(fontsize=OPTIONS['PLOT_FONT_SIZE'])
        plt.show()

    if OPTIONS['WRITE_MD']:
        write_report(cases,only_multi=OPTIONS['ONLY_MULTI'])
    if OPTIONS['LIST_ANALYZED']:
        print("\n=============================\n")
        for case in cases:
            results = case.multi_result_function_results() \
                    if OPTIONS['ONLY_MULTI'] \
                    else case.fully_analyzed_functions()
