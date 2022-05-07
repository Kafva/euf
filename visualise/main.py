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

import sys
import matplotlib.pyplot as plt
from itertools import compress
from textwrap import wrap

# '.' is needed to run from the visualise directory 
sys.path.extend(['..','.'])

from visualise.types import Case
from src.config import CONFIG
from src.types import AnalysisResult

def write_md(cases: list[Case]):
    ''' Make a MD template for the correctness analysis '''
    with open("correctness.md", mode = 'w', encoding='utf8') as f:
        for case in cases:
            f.write(f"# {case.name}\n")
            for func_result in case.function_results():
                overlap = set(func_result.results) & {AnalysisResult.SUCCESS,
                   AnalysisResult.SUCCESS_UNWIND_FAIL,
                   AnalysisResult.SUCCESS_UNWIND_FAIL,
                   AnalysisResult.FAILURE}
                if len(overlap) > 0:
                    f.write(func_result.pretty_md())
                    # Find all commits where a CBMC result
                    # was present for the current function
                    # and print an analysis command for each one
                    f.write("```bash\n")
                    for r in case.cbmc_results():
                        if r.func_name == func_result.func_name and not r.identity:
                            f.write(f"./scripts/analyze_function.sh "
                                f"{case.name.removeprefix('lib')} "
                                f"{r.func_name} "
                                f"{r.commit_old} {r.commit_new}\n"
                            )
                            f.write(f"# => {r.driver}\n")
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
    'PLOT': True,
    'LIST_ANALYZED': False,
    'UNIQUE_RESULTS': False
}

if __name__ == '__main__':
    plt.style.use('dark_background')

    CONFIG.RESULTS_DIR = ".results/5"
    onig = Case.new(name="libonig", total_functions=1186, color='#d44848')
    onig.load_change_sets()
    onig.load_impact_set()

    expat = Case.new(name="libexpat", total_functions=645, color='#32a852')
    expat.load_change_sets()
    expat.load_impact_set()

    usb = Case.new(name="libusb", total_functions=1346, color='#467fdb')
    usb.load_change_sets()
    usb.load_impact_set()

    CONFIG.RESULTS_DIR = ".results/5_impact_only"
    onig.load_change_sets(without_reduction=True)
    onig.load_impact_set(without_reduction=True)

    expat.load_change_sets(without_reduction=True)
    expat.load_impact_set(without_reduction=True)

    usb.load_change_sets(without_reduction=True)
    usb.load_impact_set(without_reduction=True)

    CONFIG.RESULTS_DIR = ".results/5"

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
        write_md(cases)
    if OPTIONS['LIST_ANALYZED']:
        print("\n=============================\n")
        for case in cases:
            case.list_fully_analyzed_functions()
