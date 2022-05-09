import os
from statistics import stdev,mean
from pprint import pprint
from dataclasses import dataclass, field
from src.config import CONFIG
from src.types import AnalysisResult, CbmcResult, \
        DependencyFunctionChange, FunctionResult
from src.util import flatten, load_cbmc_results, print_stage

ROUNDING = 4

@dataclass(init=True)
class Impacted:
    main_project_fn_name:str
    dependecy_fn_name:str

@dataclass(init=True)
class Case:
    '''
    Holds descriptive data for each case: libonig, libexpat and libusb
    '''
    total_functions: int
    name: str
    # Color to use for bar plots
    color: str

    def libname(self) -> str:
        return 'libusb-1.0' if self.name=='libusb' else self.name
    def reponame(self) -> str:
        return 'oniguruma' if self.name=='libonig' else self.name

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

    # The key to every dict is the path to the results directory
    # for a specific trial
    impact_set: dict[str,list[Impacted]] =\
            field(default_factory=dict)
    impact_set_without_reduction: dict[str,list[Impacted]] =\
            field(default_factory=dict)
    trans_set_without_reduction: dict[str,list[DependencyFunctionChange]] =\
        field(default_factory=dict)

    base_change_set: dict[str,list[DependencyFunctionChange]] =\
        field(default_factory=dict)
    reduced_change_set: dict[str,list[DependencyFunctionChange]] =\
        field(default_factory=dict)
    trans_change_set: dict[str,list[DependencyFunctionChange]] =\
        field(default_factory=dict)

    @classmethod
    def new(cls,name:str, result_dir:str, total_functions:int,color:str):
        function_results_dict, cbmc_results_dict = \
            load_cbmc_results(name,result_dir)
        return cls(name=name,
                total_functions=total_functions,
                cbmc_results_dict=cbmc_results_dict,
                function_results_dict=function_results_dict,
                color=color
        )

    def info(self,unique_results:bool=False):
        print_stage(self.name)
        changed_percent =\
            round(self.nr_of_changed_functions()/self.total_functions,
                    ROUNDING
            )
        identity_percent =\
            round(self.passed_identity_cnt()/self.nr_of_changed_functions(),
                    ROUNDING
            )
        print(f"Changed functions: "
                f"{self.nr_of_changed_functions()}/{self.total_functions} "
                f"({changed_percent})")
        print("Passed identity analysis: "
                f"{self.passed_identity_cnt()}/{self.nr_of_changed_functions()}"
                f" ({identity_percent})"
        )

        nr_of_full_analysis_results = len(list(filter(lambda c: not c.identity,
                self.cbmc_results())))
        print(f"Unique pre-analysis results: "
              f"{len(self.unique_cbmc_results(ident=True))}/"
              f"{len(self.cbmc_results())}")
        print(f"Unique full-analysis results: "
              f"{len(self.unique_cbmc_results(ident=False))}/"
              f"{nr_of_full_analysis_results}")

        multi_cnt = len(self.multi_result_function_results())
        fully_analyzed = self.fully_analyzed_functions()
        equiv_result_cnt = len(list(filter(lambda x:
            1 <= len({
                AnalysisResult.SUCCESS,
                AnalysisResult.SUCCESS_UNWIND_FAIL
                } | set(x.results)) <= 2 ,
            fully_analyzed
        )))
        influential_result_cnt = len(list(filter(lambda x:
            1 <= len({
                AnalysisResult.FAILURE,
                AnalysisResult.FAILURE_UNWIND_FAIL
                } | set(x.results)) <= 2 ,
            fully_analyzed
        )))

        print(f"Functions with an influential and equivalent analysis result: "
              f"{multi_cnt}/{self.nr_of_changed_functions()}")
        print(f"Functions with \033[4monly\033[0m equivalent analysis results: "
              f"{equiv_result_cnt}/{self.nr_of_changed_functions()}")
        print(f"Functions with \033[4monly\033[0m influential analysis results: "
              f"{influential_result_cnt}/{self.nr_of_changed_functions()}")

        dupes = "\033[4mwithout duplicates\033[0m" if unique_results else \
            "\033[4mwith duplicates\033[0m"
        print(f"Result distribution {dupes} (pre-analysis):")
        pprint(self.sorted_analysis_dist(
            ident=True,filter_zero=True,unique_results=False)
        )
        print(f"Result distribution {dupes} (full-analysis):")
        pprint(self.sorted_analysis_dist(
            ident=False,filter_zero=True,unique_results=False)
        )

        change_set_sizes = [ len(v) for v in self.base_change_set.values() ]
        trans_set_sizes = [ len(v) for v in self.trans_change_set.values() ]
        impact_set_sizes = [ len(v) for v in self.impact_set.values() ]

        self.average_set(change_set_sizes,
            self.change_set_reductions_per_trial(),
            "change"
        )
        self.average_set(trans_set_sizes,
            self.trans_set_reductions_per_trial(),
            "transitive"
        )
        self.average_set(impact_set_sizes,
            self.impact_set_reductions_per_trial(),
            "impact"
        )

    def average_set(self, sizes: list[int], reductions:list[float], label:str):
        average_size = round(mean(sizes),ROUNDING)
        stdev_size = round(stdev(sizes),ROUNDING)
        print(f"Average {label} set size: {average_size} (±{stdev_size})")

        mean_reduction = round(mean(reductions),ROUNDING)
        stdev_reduction = round(stdev(reductions),ROUNDING)
        print(f"Average {label} set reduction: {mean_reduction} (±{stdev_reduction})")

    def impact_set_reductions_per_trial(self) -> list[float]:
        reductions_per_trial = []
        for d,d_without in zip(self.impact_set,self.impact_set_without_reduction):
            assert len(self.impact_set_without_reduction[d_without]) >= \
                    len(self.impact_set[d])

            reductions_per_trial.append(
                    len(self.impact_set_without_reduction[d_without]) -
                    len(self.impact_set[d])
            )
        return reductions_per_trial

    def trans_set_reductions_per_trial(self) -> list[float]:
        reductions_per_trial = []
        for d,d_without in \
          zip(self.trans_change_set,self.trans_set_without_reduction):
            without_reduction = len(self.trans_set_without_reduction[d_without])
            with_reduction = len(self.trans_change_set[d])

            assert without_reduction >= with_reduction
            reductions_per_trial.append(
                    len(self.trans_set_without_reduction[d_without]) -
                    len(self.trans_change_set[d])
            )

        return reductions_per_trial

    def change_set_reductions_per_trial(self) -> list[float]:
        '''
        Go through each pair of base and reduced change sets and record the
        reduction for each one.
        '''
        reductions_per_trial = []
        for dirpath in self.base_change_set:
            assert len(self.base_change_set[dirpath]) >= \
                    len(self.reduced_change_set[dirpath])
            reductions_per_trial.append(
                    len(self.base_change_set[dirpath]) -
                    len(self.reduced_change_set[dirpath])
            )
        return reductions_per_trial

    def multi_result_function_results(self,ident:bool=False) -> list[FunctionResult]:
        multi_results = []
        for func_res in self.function_results():
            if func_res.has_multi_result(ident):
                multi_results.append(func_res)
        return multi_results

    def fully_analyzed_functions(self) -> list[FunctionResult]:
        '''
        Return a list of all functions that passed the identity analysis
        '''
        fully_analyzed = []
        for function_result in self.function_results():
            if len(function_result.results)>0:
                fully_analyzed.append(function_result)
        return fully_analyzed

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

    def sorted_analysis_dist(self,ident:bool,
      filter_zero:bool,unique_results:bool):
        li = [ (key.name,round(val,ROUNDING)) for key,val in
                self.analysis_dist(
                    ident=ident,
                    filter_zero=filter_zero,
                    unique_results=unique_results
                ).items()
        ]
        return sorted(li, key=lambda l: l[1], reverse=True)

    def unique_cbmc_results(self,ident:bool):
        return set(map(lambda c: (c.func_name,c.result),
                filter(lambda r: r.identity == ident,
                    self.cbmc_results()
                ))
            )

    def analysis_dist(self,
     ident:bool,
     filter_zero:bool=False,
     combine_unwinds:bool=False,
     unique_results:bool=False
     ) -> dict[AnalysisResult,float]:
        '''
        Returns a dict of percentages for each AnalysisResult
        across every function analysis (during either the full or ID stage).
        The list starts with the first entry in the AnalysisResult enum 
        '''
        if ident:
            # Pre-analysis was performed for every function
            # in function_results
            analysis_steps_performed = sum(map(lambda f: len(f.results_id),
                self.function_results()))
        else:
            # Functions which did not pass the identity check will have
            # a results array with len()==0
            analysis_steps_performed = sum(map(lambda f: len(f.results),
                self.function_results()))

        filtered_cbmc_results = filter(lambda c: c.identity == ident,
                self.cbmc_results())

        result_cnts = { e.name: 0 for e in AnalysisResult }

        if unique_results:
            # Only increment the result count for unique entries,
            # e.g. count 16 SUCCESS results for a function as 1 SUCCESS
            # This also requires the analysis_steps_performed to be reduced
            # for percentages to be correct
            unique_cbmc_results = self.unique_cbmc_results(ident=ident)

            for tpl in unique_cbmc_results:
                result_cnts[tpl[1].name] += 1

            analysis_steps_performed = len(unique_cbmc_results)
        else:
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

        assert (sum([ x for x in analysis_dict.values() ]) - 1) < 10**-12
        return analysis_dict

    def load_change_set(self,dirpath:str,filename:str,
     change_set:dict[str,list[DependencyFunctionChange]]):
        if os.path.isfile(f"{dirpath}/{filename}"):
            with open(f"{dirpath}/{filename}", mode='r', encoding='utf8') as f:
                for line in f.readlines()[1:]:
                    change_set[dirpath].append(DependencyFunctionChange.\
                            new_from_change_set_csv(line.split(";"))
                    )

    def load_change_sets(self,without_reduction:bool=False):
        for item in os.listdir(CONFIG.RESULTS_DIR):
            dirpath = f"{CONFIG.RESULTS_DIR}/{item}"
            # Only load entries matching the current name
            if os.path.isdir(dirpath) and item.startswith(self.name):
                if without_reduction:
                    self.trans_set_without_reduction[dirpath] = []

                    self.load_change_set(dirpath, "trans_change_set.csv",
                            self.trans_set_without_reduction)
                else:
                    self.base_change_set[dirpath] = []
                    self.reduced_change_set[dirpath] = []
                    self.trans_change_set[dirpath] = []

                    self.load_change_set(dirpath, "change_set.csv",
                            self.base_change_set)
                    self.load_change_set(dirpath, "reduced_set.csv",
                            self.reduced_change_set)
                    self.load_change_set(dirpath, "trans_change_set.csv",
                            self.trans_change_set)


        # The number of changed functions in the base set and the functions
        # from cbmc analysis should be equal
        assert len(self.base_change_set) == len(self.cbmc_results_dict)

    def load_impact_set(self,without_reduction:bool=False):
        for item in os.listdir(CONFIG.RESULTS_DIR):
            dirpath = f"{CONFIG.RESULTS_DIR}/{item}"

            # Only load entries matching the current name
            if os.path.isdir(dirpath) and item.startswith(self.name):
                if without_reduction:
                    self.impact_set_without_reduction[dirpath] = []
                else:
                    self.impact_set[dirpath] = []

                if os.path.isfile(f"{dirpath}/impact_set.csv"):
                    with open(f"{dirpath}/impact_set.csv",
                      mode = 'r', encoding='utf8') as f:
                        for line in f.readlines()[1:]:
                            csv_values = line.split(";")
                            if without_reduction:
                                self.impact_set_without_reduction[dirpath]\
                                    .append(Impacted(
                                    main_project_fn_name=csv_values[3],
                                    dependecy_fn_name=csv_values[8]
                                ))
                            else:
                                self.impact_set[dirpath].append(Impacted(
                                    main_project_fn_name=csv_values[3],
                                    dependecy_fn_name=csv_values[8]
                                ))