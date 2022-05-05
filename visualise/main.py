#!/usr/bin/env python3
'''
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
    - "description" should motivate the trusted column"s value (seperate
      markdown doc, with pictures)


  * Plotting (per case):
      Bar diagram with AnalysisResult distrubtion (with and without
              *_unwind joint togheter)

'''
import sys, os
import matplotlib.pyplot as plt
from dataclasses import dataclass, field
from datetime import datetime

# '.' is needed to run the script from ./scripts
sys.path.extend(['..','.'])

from src.config import CONFIG
from src.types import AnalysisResult, IdentifierLocation
from src.util import print_info, print_stage

@dataclass(init=True)
class CbmcResult:
    func_name:str
    identity:bool
    result: AnalysisResult
    runtime: datetime
    driver: str
    location_old: IdentifierLocation
    location_new: IdentifierLocation

    @classmethod
    def new(cls, items:list):
        assert len(items) == 13
        return cls(
            func_name = items[0],
            identity = items[1] == "True",
            result = AnalysisResult[items[2]],
            runtime = datetime.now(),
            driver = items[4],
            location_old = IdentifierLocation(
                _filepath = items[5],
                line = items[6],
                column = items[7],
                name = items[8].strip()
            ),
            location_new = IdentifierLocation(
                _filepath = items[9],
                line = items[10],
                column = items[11],
                name = items[12].strip()
            ),
        )

@dataclass(init=True)
class FunctionResult:
    '''
    A list of all the analysis results recorded for a perticular
    function. By using a list with duplicate entries we can
    see the distrubtion of results and fetch a set()
    '''
    func_name: str
    results: list[AnalysisResult]    = field(default_factory=list)
    results_id: list[AnalysisResult] = field(default_factory=list)

    def pretty(self,ident:bool=False) -> str:
        out = f"{self.func_name}: [\n"
        res = self.results_id if ident else self.results
        for r in set(res):
            cnt = res.count(r)
            out += f"{CONFIG.INDENT}{r.name} ({cnt}),\n"
        return out.strip(",\n")+"\n]"

def get_function_results(name:str) -> \
tuple[dict[str,FunctionResult],dict[str,list[CbmcResult]]]:
    print_stage(name)
    function_results = {}
    cbmc_results = {}

    for item in os.listdir(CONFIG.RESULTS_DIR):
        dirpath = f"{CONFIG.RESULTS_DIR}/{item}"
        cbmc_results[dirpath] = []

        if os.path.isdir(dirpath) and item.startswith(name):
            if os.path.isfile(f"{dirpath}/cbmc.csv"):
                with open(f"{dirpath}/cbmc.csv", mode = 'r', encoding='utf8') as f:
                    for line in f.readlines()[1:]:
                        cbmc_results[dirpath].append(CbmcResult.new(line.split(";")))

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

def brief(function_results: dict[str,FunctionResult]):
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
            AnalysisResult.ERROR in v.results,
            function_results.values()
    ))

    #for s in successes: print(s.pretty(ident=True))
    print_info(f"Successes: {len(successes)}")
    print_info(f"Failures: {len(failures)}")
    print_info(f"Errors: {len(errors)}")

def plot_result_distribution(
 cbmc_results: dict[str,list[CbmcResult]],
 ident:bool=False):
    '''
    Create a plot showing the distribution of results from each item
    in the provided cbmc_results list
    '''
    result_cnts = { e.name: 0 for e in AnalysisResult }
    for cbmc_list in cbmc_results.values():
        filtered = filter(lambda x: x.identity == ident, cbmc_list)
        for c in filtered:
            result_cnts[c.result.name] += 1

    # Exclude results that never occured
    result_cnts = { key: val for key,val in result_cnts.items() if val != 0 }

    # Combine _unwind cases
    result_cnts[AnalysisResult.SUCCESS.name] += \
        result_cnts[AnalysisResult.SUCCESS_UNWIND_FAIL.name]
    result_cnts[AnalysisResult.FAILURE.name] += \
        result_cnts[AnalysisResult.FAILURE_UNWIND_FAIL.name]
    del result_cnts[AnalysisResult.SUCCESS_UNWIND_FAIL.name]
    del result_cnts[AnalysisResult.FAILURE_UNWIND_FAIL.name]

    # Color each bar based on the case

    plt.bar(
        list(result_cnts.keys()),
        list(result_cnts.values())
    )
    plt.show()

if __name__ == '__main__':
    CONFIG.RESULTS_DIR = ".results"
    onig_results, onig_cbmc = get_function_results("libonig")
    expat_results, expat_cbmc = get_function_results("libexpat")
    usb_results, usb_cbmc = get_function_results("libusb")


    brief(onig_results)
    plot_result_distribution(onig_cbmc)
