import os,re
from pprint import pprint
from dataclasses import dataclass, field
from datetime import datetime
from src.config import CONFIG
from src.types import AnalysisResult, IdentifierLocation
from src.util import flatten, print_stage

@dataclass(init=True)
class CbmcResult:
    func_name:str
    identity:bool
    result: AnalysisResult
    runtime: datetime
    driver: str
    location_old: IdentifierLocation
    location_new: IdentifierLocation
    commit_old: str
    commit_new: str

    @classmethod
    def new(cls, items:list, directory:str):
        assert len(items) == 13

        commit_old = re.search(r"_[a-z0-9]{4}_", directory).\
                group(0)[1:-1] # type: ignore
        commit_new = re.search(r"_[a-z0-9]{4}$", directory).\
                group(0)[1:] # type: ignore

        return cls(
            func_name = items[0],
            identity = False if items[1] == "False" else True,
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
            commit_old = commit_old,
            commit_new = commit_new
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

    def pretty_md(self,ident:bool=False) -> str:
        out = f"## `{self.func_name}()`\n"
        res = self.results_id if ident else self.results
        for r in set(res):
            cnt = res.count(r)
            out += f"> {r.name} ({cnt})\n"
        return out

@dataclass(init=True)
class Case:
    '''
    Holds descriptive data for each case: libonig, libexpat and libusb


    '''
    total_functions: int
    name: str

    # Holds one entry per function that was analyzed (dict key),
    # each item contains an array of AnalysisResult that
    # were encountered for the particular function
    # during full and identity analysis
    function_results_dict: dict[str,FunctionResult]

    def function_results(self) -> list[FunctionResult]:
        return [ r for r in self.function_results_dict.values() ]

    # Holds one entry per CSV row across all results, dict key
    # is the path to the CSV file
    cbmc_results_dict: dict[str,list[CbmcResult]]

    def cbmc_results(self) -> list[CbmcResult]:
        return flatten([ r for r in self.cbmc_results_dict.values() ])

    @classmethod
    def load_from_csv_files(cls,name:str) -> \
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

    @classmethod
    def new(cls,name:str,total_functions:int):
        function_results_dict, cbmc_results_dict = cls.load_from_csv_files(name)

        return cls(name=name,
                total_functions=total_functions,
                cbmc_results_dict=cbmc_results_dict,
                function_results_dict=function_results_dict
        )

    def info(self):
        print_stage(self.name)
        changed_percent =\
            round(self.nr_of_changed_functions()/self.total_functions,4)
        identity_percent =\
            round(self.passed_identity_cnt()/self.nr_of_changed_functions(),4)
        print(f"Changed functions: "
                f"{self.nr_of_changed_functions()}/{self.total_functions} ({changed_percent})")
        print("Passed identity analysis: "
                f"{self.passed_identity_cnt()}/{self.nr_of_changed_functions()} "
                f"({identity_percent})"
        )
        print("Result distribution (pre-analysis):")
        pprint(self.analysis_dist(ident=True,filter_zero=True))
        print("Result distribution (full-analysis):")
        pprint(self.analysis_dist(ident=False,filter_zero=True))


    def nr_of_changed_functions(self) -> int:
        ''' The total number of analyzed functions corresponds to the number of
        functions that were observed as changed in at least one case,
        every changed function will generate a CBMC entry even if 
        it cannot be analyzed in `valid_preconds()` '''
        return len(self.function_results())

    def passed_identity_cnt(self) -> int:
        '''
        Out of the functions that were analyzed, how many passed
        the identity comparision 

        Note: We know that the total number of full analyses that were
        performed will be equal to the number of successful ID comparisons
        '''
        funcs_with_at_least_one_valid_id_cmp = list(filter(lambda v:
                AnalysisResult.SUCCESS in v.results_id or
                AnalysisResult.SUCCESS_UNWIND_FAIL in v.results_id,
                self.function_results()
        ))
        return len(funcs_with_at_least_one_valid_id_cmp)

    def analysis_dist(self,
     ident:bool,
     filter_zero:bool=False,
     combine_unwinds:bool=False,
     ) -> dict[AnalysisResult,float]:
        ''' Returns a dict of percentages for each AnalysisResult
        across every function analysis (during either the full or ID stage). 
        The list starts with the first entry in the AnalysisResult enum '''
        if ident:
            # Identity analysis was performed for every function 
            # in function_results
            analysis_steps_performed = sum(map(lambda f: len(f.results_id),
                self.function_results()))
        else:
            # Functions which did not pass the identity check will have len()==0
            # of their results array.
            analysis_steps_performed = sum(map(lambda f: len(f.results),
                self.function_results()))

        filtered_cbmc_results = filter(lambda c: c.identity == ident,
                self.cbmc_results())

        result_cnts = { e.name: 0 for e in AnalysisResult }
        for cbmc_result in filtered_cbmc_results:
            result_cnts[cbmc_result.result.name] += 1

        if combine_unwinds:
            result_cnts[AnalysisResult.SUCCESS.name] += \
                result_cnts[AnalysisResult.SUCCESS_UNWIND_FAIL.name]
            result_cnts[AnalysisResult.FAILURE.name] += \
                result_cnts[AnalysisResult.FAILURE_UNWIND_FAIL.name]
            del result_cnts[AnalysisResult.SUCCESS_UNWIND_FAIL.name]
            del result_cnts[AnalysisResult.FAILURE_UNWIND_FAIL.name]

        if filter_zero:
            result_cnts = { key: val
                    for key,val in result_cnts.items() if val != 0
            }

        analysis_dict = { AnalysisResult[tpl[0]]: tpl[1]/analysis_steps_performed
                for tpl in result_cnts.items() }

        assert sum([ x for x in analysis_dict.values() ]) == 1
        return analysis_dict


