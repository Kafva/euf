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
  * How are the Analysis Results distributed?
      * Plotting the mean for each type of result from each case could be somewhat
        interesting as well
  * Reduction in change and impact set (mean,lowest,highest graph)
  * Table of the SUCCESS and FAILURE analyzed functions


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
from src.util import flatten

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

def plot_analysis_dists(cases: list[Case],ident:bool=False):
    cases_dists = [ c.analysis_dist(ident=ident).values() for c in cases ]

    non_zero_fields = [ a!=0 or b!=0 or c!=0 for a,b,c in
            zip(cases_dists[0],
                cases_dists[1],
                cases_dists[2]) ]

    # Remove fields that are zero across all cases
    cases_dists = [ list(compress(c,non_zero_fields)) for c in cases_dists ]


    bar_names = [ e.name for e in AnalysisResult ]
    bar_names  = list(compress(bar_names, non_zero_fields))

    # Wrap the bar name text to X chars
    bar_names = [ '\n'.join(wrap(l, 10)) for l in bar_names ]

    _, axes = plt.subplots()
    width = 0.35

    # Color-code a bar plot for each case
    for i,case in enumerate(cases):
        # The bottom value must be correctly set to the sum of the previous 
        # bars, otherwise overlaps will occur
        match i:
            case 1: bottom = cases_dists[0]
            case 2: bottom = [ x+y for x,y in zip(cases_dists[0],cases_dists[1]) ]
            case _: bottom = 0

        axes.bar(bar_names, cases_dists[i],  width,  label=case.name, bottom = bottom)

    axes.set_ylabel('')
    axes.set_title(f"Distribution of CBMC {'identity ' if ident else ''}analysis results")
    axes.legend()

    plt.xticks(fontsize=10)
    plt.show()

if __name__ == '__main__':
    WRITE_MD = True
    PLOT = True
    CONFIG.RESULTS_DIR = ".results/5"

    onig = Case.new(name="libonig", total_functions=1186)
    onig.info()
    expat = Case.new(name="libexpat", total_functions=645)
    expat.info()
    usb = Case.new(name="libusb", total_functions=1346)
    usb.info()

    cases = [onig,expat,usb]

    if PLOT:
        plot_analysis_dists(cases,ident=True)
        plot_analysis_dists(cases,ident=False)
    if WRITE_MD:
        write_md(cases)


