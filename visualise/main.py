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
  * How many of each type of results were derived from each analysis?
      * Plotting the mean for each type of result from each case could be somewhat
        interesting as well
  * Reduction in change and impact set (mean,lowest,highest graph)
  * Table of the SUCCESS and FAILURE analyzed functions


'''
import sys, os
import matplotlib.pyplot as plt
from itertools import compress
from textwrap import wrap

# '.' is needed to run from the visualise directory 
sys.path.extend(['..','.'])

from visualise.types import CbmcResult, FunctionResult
from src.config import CONFIG
from src.types import AnalysisResult
from src.util import print_info, print_stage

def get_results_from_csv(name:str) -> \
 tuple[dict[str,FunctionResult],dict[str,list[CbmcResult]]]:
    function_results = {}
    cbmc_results = {}

    for item in os.listdir(CONFIG.RESULTS_DIR):
        dirpath = f"{CONFIG.RESULTS_DIR}/{item}"
        cbmc_results[dirpath] = []

        if os.path.isdir(dirpath) and item.startswith(name):
            if os.path.isfile(f"{dirpath}/cbmc.csv"):
                with open(f"{dirpath}/cbmc.csv", mode = 'r', encoding='utf8') as f:
                    for line in f.readlines()[1:]:
                        cbmc_results[dirpath].append(
                            CbmcResult.new(line.split(";"), dirpath)
                        )

                        # Add a key for each function name
                        func_name = cbmc_results[dirpath][-1].func_name
                        if func_name not in function_results:
                            function_results[func_name] =\
                            FunctionResult(func_name=func_name)

        # Join entries with for the same function into one
        for func_name,func_result in function_results.items():
            func_result.results.extend(
                map(lambda a: a.result, filter(lambda c:
                    not c.identity and c.func_name == func_name,
                    cbmc_results[dirpath]
                )
            ))
            func_result.results_id.extend(
                map(lambda a: a.result, filter(lambda c:
                    c.identity and c.func_name == func_name,
                    cbmc_results[dirpath]
                )
            ))

    return function_results, cbmc_results

def correctness_per_function(name:str,
 function_results: dict[str,FunctionResult], ident:bool=False):
    msg = name + (" (identity)" if ident else '')
    print_stage(msg)

    if ident:
        successes = list(filter(lambda v:
                AnalysisResult.SUCCESS in v.results_id or
                AnalysisResult.SUCCESS_UNWIND_FAIL in v.results_id,
                function_results.values()
        ))
        failures = list(filter(lambda v:
                AnalysisResult.FAILURE in v.results_id or
                AnalysisResult.FAILURE_UNWIND_FAIL in v.results_id,
                function_results.values()
        ))
        errors = list(filter(lambda v:
                AnalysisResult.ERROR in v.results or
                AnalysisResult.STRUCT_CNT_CONFLICT in v.results_id or
                AnalysisResult.STRUCT_TYPE_CONFLICT in v.results_id,
                function_results.values()
        ))
    else:
        successes = list(filter(lambda v:
                AnalysisResult.SUCCESS in v.results or
                AnalysisResult.SUCCESS_UNWIND_FAIL in v.results,
                function_results.values()
        ))
        failures = list(filter(lambda v:
                AnalysisResult.FAILURE in v.results or
                AnalysisResult.FAILURE_UNWIND_FAIL in v.results,
                function_results.values()
        ))
        errors = list(filter(lambda v:
                AnalysisResult.ERROR in v.results or
                AnalysisResult.STRUCT_CNT_CONFLICT in v.results or
                AnalysisResult.STRUCT_TYPE_CONFLICT in v.results,
                function_results.values()
        ))


    if DUMP_SUCCESS:
        for s in successes: print(s.pretty(ident=ident))
    print_info(f"Successes: {len(successes)}")
    print_info(f"Failures: {len(failures)}")
    print_info(f"Errors: {len(errors)}")

def get_result_distribution(cbmc_results: dict[str,list[CbmcResult]],
 ident:bool=False) -> tuple[list[str],list[int]]:
    '''
    Create a plot showing the distribution of results from each item
    in the provided cbmc_results list
    '''
    result_cnts = { e.name: 0 for e in AnalysisResult }
    for cbmc_list in cbmc_results.values():
        filtered = filter(lambda x: x.identity == ident, cbmc_list)
        for c in filtered:
            result_cnts[c.result.name] += 1

    # Combine _unwind cases
    result_cnts[AnalysisResult.SUCCESS.name] += \
        result_cnts[AnalysisResult.SUCCESS_UNWIND_FAIL.name]
    result_cnts[AnalysisResult.FAILURE.name] += \
        result_cnts[AnalysisResult.FAILURE_UNWIND_FAIL.name]
    del result_cnts[AnalysisResult.SUCCESS_UNWIND_FAIL.name]
    del result_cnts[AnalysisResult.FAILURE_UNWIND_FAIL.name]

    # Exclude results that never occured in any of the cases
    #result_cnts = { key: val for key,val in result_cnts.items() if val != 0 }

    bar_names = list(result_cnts.keys())

    # Wrap the bar name text to X chars
    bar_names = [ '\n'.join(wrap(l, 10)) for l in bar_names ]

    bar_values = list(result_cnts.values())
    return bar_names, bar_values

def write_md():
    ''' Make a MD template for the correctness analysis '''
    with open("correctness.md", mode = 'w', encoding='utf8') as f:
        for i,test_case_result in enumerate(TEST_CASE_RESULTS):
            f.write(f"# {TEST_LIBS[i]}\n")
            for _, func_result in test_case_result.items():
                overlap = set(func_result.results) & {AnalysisResult.SUCCESS,
                   AnalysisResult.SUCCESS_UNWIND_FAIL,
                   AnalysisResult.SUCCESS_UNWIND_FAIL,
                   AnalysisResult.FAILURE}
                if len(overlap) > 0:
                    f.write(func_result.pretty_md())
                    # Find all commits where a CBMC result
                    # was present for the current function
                    # and print an analysis command for each one
                    for cbmc_result in TEST_CASE_CBMCS[i].values():
                        for r in cbmc_result:
                            if r.func_name == func_result.func_name:
                                f.write(f"> ./scripts/analyze_function.sh "
                                    f"{r.func_name} "
                                    f"{r.commit_old} {r.commit_new}\n"
                                )
                    f.write("\n\n")

def result_dists(bar_names,onig_cnts,expat_cnts,usb_cnts,ident:bool=False):
    '''
    Exclude AnalysisResult cases which had zero occurrences 
    for all cases
    '''
    non_zero_fields = [ a!=0 or b!=0 or c!=0 for a,b,c in
            zip(onig_cnts,expat_cnts,usb_cnts) ]

    bar_names  = list(compress(bar_names, non_zero_fields))
    onig_cnts  = list(compress(onig_cnts, non_zero_fields))
    expat_cnts = list(compress(expat_cnts, non_zero_fields))
    usb_cnts   = list(compress(usb_cnts, non_zero_fields))

    _, axes = plt.subplots()
    width = 0.35

    # Color-code a bar plot for each case
    axes.bar(bar_names, onig_cnts,  width,  label='libonig')
    axes.bar(bar_names, expat_cnts, width,  label='libexpat')
    axes.bar(bar_names, usb_cnts,   width,  label='libusb')

    axes.set_ylabel('Occurrences')
    axes.set_title(f"Distribution of CBMC {'identity ' if ident else ''}analysis results")
    axes.legend()


    plt.xticks(fontsize=10)
    plt.show()

if __name__ == '__main__':
    PLOT = True
    DUMP_SUCCESS = True
    CONFIG.RESULTS_DIR = ".results/1"

    onig_results, ONIG_CBMC = get_results_from_csv("libonig")
    correctness_per_function("libonig", onig_results, ident=False)
    correctness_per_function("libonig", onig_results, ident=True)

    expat_results, EXPAT_CBMC = get_results_from_csv("libexpat")
    correctness_per_function("libexpat", expat_results, ident=False)
    correctness_per_function("libexpat", expat_results, ident=True)

    usb_results, USB_CBMC = get_results_from_csv("libusb")
    correctness_per_function("libusb", usb_results, ident=False)
    correctness_per_function("libusb", usb_results, ident=True)

    TEST_LIBS = ["libonig", "libexpat", "libusb"]
    TEST_CASE_RESULTS = [onig_results, expat_results, usb_results]
    TEST_CASE_CBMCS = [ONIG_CBMC, EXPAT_CBMC, USB_CBMC]
    write_md()

    if PLOT:
        bar_names, onig_cnts = get_result_distribution(ONIG_CBMC)
        _, expat_cnts = get_result_distribution(EXPAT_CBMC)
        _, usb_cnts = get_result_distribution(USB_CBMC)

        result_dists(bar_names,onig_cnts,expat_cnts,usb_cnts)

        bar_names, onig_cnts = get_result_distribution(ONIG_CBMC,ident=True)
        _, expat_cnts = get_result_distribution(EXPAT_CBMC,ident=True)
        _, usb_cnts = get_result_distribution(USB_CBMC,ident=True)

        result_dists(bar_names,onig_cnts,expat_cnts,usb_cnts,ident=True)

