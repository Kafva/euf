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
from dataclasses import dataclass
from datetime import datetime
import sys, os

# '.' is needed to run the script from ./scripts
sys.path.extend(['..','.'])

from src.config import CONFIG
from src.types import AnalysisResult, IdentifierLocation

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
    def new(cls,items:list):
        assert len(items) == 13
        return cls(
            func_name = items[0],
            identity = items[1] == "True",
            result = AnalysisResult(1), # TODO
            runtime = datetime.now(),
            driver = items[4],
            location_old = IdentifierLocation(
                _filepath = items[5],
                line = items[6],
                column = items[7],
                name = items[8]
            ),
            location_new = IdentifierLocation(
                _filepath = items[9],
                line = items[10],
                column = items[11],
                name = items[12]
            ),
        )




def get_case(name:str):
    for item in os.listdir(CONFIG.RESULTS_DIR):

        dirpath = f"{CONFIG.RESULTS_DIR}/{item}"
        if os.path.isdir(dirpath) and item.startswith(name):

            if os.path.isfile(f"{dirpath}/cbmc.csv"):
                with open(f"{dirpath}/cbmc.csv", mode = 'r', encoding='utf8') as f:
                    for line in f.readlines():
                        r = CbmcResult.new(line.split(";"))
                        print(r)

get_case("libonig")
