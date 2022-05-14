import os
from posixpath import expanduser
from textwrap import wrap
from itertools import compress

import matplotlib.pyplot as plt
from matplotlib.figure import Figure

from src.config import CONFIG
from src.types import AnalysisResult
from visualise.case import Case
from visualise import OPTIONS

def write_report(cases: list[Case], only_multi:bool=False):
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

def plot_analysis_dists(cases: list[Case],ident:bool=False) -> Figure:
    '''
    Not using the `unique_results` option gives the impression that expat has
    very good performance, which stems from the fact that it has analyzed
    the same few functions successfully many times.
    '''
    fig = plt.figure(figsize=OPTIONS['FIG_SIZE'])
    subfigs = fig.subfigures(nrows=2, ncols=1)

    def create_row(title,index,unique_results:bool):
        subfigs[index].suptitle(title,fontweight='bold',
                horizontalalignment='center'
        )
        axes = subfigs[index].subplots(nrows=1, ncols=1)
        axes.set_ylabel('')

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

        # Color-code a bar plot for each case
        for i,case in enumerate(cases):
            # The bottom value must be correctly set to the sum of the previous
            # bars, otherwise overlaps will occur
            match i:
                case 1: bottom = cases_dists[0]
                case 2: bottom = [ x+y for x,y in zip(cases_dists[0],cases_dists[1]) ]
                case _: bottom = 0

            axes.bar(bar_names, cases_dists[i],
                    width = OPTIONS['PLOT_WIDTH'],
                    label = case.name,
                    color = [ cases[i].color ],
                    bottom = bottom,
                    edgecolor='white'
            )

        if index==0:
            axes.legend(loc='upper left')

    title = f"Distribution of CBMC {'identity ' if ident else ''}analysis "\
            "results (with duplicates)"

    create_row(title,0,unique_results=False)
    create_row("Without duplicates",1,unique_results=True)

    return fig

def plot_reductions(cases: list[Case],percent:bool=True) -> Figure:
    '''
    We want to show the average reduction, stdev from the average and the
    extreme values, a violin plot is somewhat suitable for this
    '''
    change_set_reductions = [ c.change_set_reductions_per_trial(percent=percent)
            for c in cases ]
    trans_set_reductions =  [ c.trans_set_reductions_per_trial(percent=percent)
            for c in cases ]
    impact_set_reductions = [ c.impact_set_reductions_per_trial(percent=percent)
            for c in cases ]

    fig = plt.figure(figsize=OPTIONS['FIG_SIZE'])
    subfigs = fig.subfigures(nrows=3, ncols=1)

    def create_row(title,index,array1,label):
        subfigs[index].suptitle(title,
            fontweight='bold',
            horizontalalignment='center'
        )
        axes = subfigs[index].subplots(nrows=1, ncols=3)
        unit = '%' if percent else '#'
        axes[0].set_ylabel(f"Items removed from {label} set [{unit}]")

        for i, ax in enumerate(axes):
            parts = ax.violinplot(
                array1[i],
                showmeans=True, showextrema=True
            )
            if percent:
                ax.set_ylim(OPTIONS['VIOLIN_YLIM'])

            for pc in parts['bodies']:
                pc.set_facecolor(OPTIONS['PINK'])
                pc.set_edgecolor('white')
                pc.set_alpha(0.5)

            # Change colors of the mean indicators
            for partname in ('cbars','cmins','cmaxes','cmeans'):
                vp = parts[partname]
                vp.set_edgecolor(OPTIONS['DARK PINK'])
                vp.set_linewidth(2)

            if index==2:
                ax.set_xlabel(cases[i].name,
                    fontweight='normal',
                    fontsize=12,
                    horizontalalignment='center',
                )

    create_row("Base change set reduction", 0, change_set_reductions,
        "change"
    )
    create_row("Transitive change set reduction", 1, trans_set_reductions,
        "transitive"
    )
    create_row("Impact set reduction", 2, impact_set_reductions,
        "impact"
    )

    return fig

def plot_states():
    '''
    Each state space analysis creates a states.json file on the form:
    "ENTROPY_DEBUG": {
      "parameters": [
          {
              "name": "label",
              "nondet": false,
              "states": [
                  "arc4random_buf"
              ]
          },
          {
              "name": "entropy",
              "nondet": true,
              "states": []
          }
      ]
    }

    For the visualisation we would like to know (per case):
        * What percentage of (analyzed/changed) functions had at least 
        one parameter with constant state?

        * Out of the functions with at least one constant parameter, how many states
        were encountered for a parameter on average?

        * Did any state space anylsis yield a harness where every parameter was
        constrained? I.e. what percentage of parameters in a function were
        constrained on average?

    This data would highlight how useful state analysis is in regards to limiting
    the data space of input data.
    '''
    # pylint: disable=unnecessary-pass
    pass

