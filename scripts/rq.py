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
'''
import sys, os
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
    # A list of all the analysis results recorded for a perticular
    # function. By using a list with duplicate entries we can
    # see the distrubtion of results and fetch a set()
    func_name: str
    results: list[AnalysisResult] = field(default_factory=list)
    results_id: list[AnalysisResult] = field(default_factory=list)


    #@classmethod
    #def new(cls, list[CbmcResult]):


def get_case(name:str):
    print_stage(name)

    function_results = {}

    for item in os.listdir(CONFIG.RESULTS_DIR):

        cbmc_results = []
        dirpath = f"{CONFIG.RESULTS_DIR}/{item}"

        if os.path.isdir(dirpath) and item.startswith(name):

            if os.path.isfile(f"{dirpath}/cbmc.csv"):
                with open(f"{dirpath}/cbmc.csv", mode = 'r', encoding='utf8') as f:
                    for line in f.readlines()[1:]:
                        cbmc_results.append(CbmcResult.new(line.split(";")))

                        # Add a key for each function name
                        func_name = cbmc_results[-1].func_name
                        if func_name not in function_results:
                            function_results[func_name] =\
                            FunctionResult(func_name=func_name)


        # Join entries with for the same function into one
        for func_name,func_result in function_results.items():
            func_result.results.extend(
                map(lambda a: a.result, filter(lambda c:
                    not c.identity and c.func_name == func_name,
                    cbmc_results
                )
            ))
            func_result.results_id.extend(
                map(lambda a: a.result, filter(lambda c:
                    c.identity and c.func_name == func_name,
                    cbmc_results
                )
            ))

    successes = list(filter(lambda v:
            AnalysisResult.SUCCESS in v.results or
            AnalysisResult.SUCCESS_UNWIND_FAIL in v.results,
            function_results.values()
    ))

    __import__('pprint').pprint(successes)

    #print_info(f"Failures: {len(failures)}")
    print_info(f"Successes: {len(successes)}")

get_case("libonig")
