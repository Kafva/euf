from statistics import stdev,mean
from dataclasses import dataclass, field
from src.types import AnalysisResult, CbmcResult, \
        DependencyFunctionChange, FunctionResult, StateParam
from src.util import flatten, load_cbmc_results, print_err, print_stage
from visualise import OPTIONS

from visualise.deserialise import Impacted, \
    load_change_sets, load_impact_set, load_state_space

ROUNDING = 4

def average_set(sizes: list[int], reductions:list[float], label:str):
    average_size = round(mean(sizes),ROUNDING)
    stdev_size = round(stdev(sizes),ROUNDING)
    print(f"Average {label} set size: {average_size} (±{stdev_size})")

    mean_reduction = round(mean(reductions),ROUNDING)
    stdev_reduction = round(stdev(reductions),ROUNDING)
    print(f"Average {label} set reduction: {mean_reduction} (±{stdev_reduction})")

def basic_dist(msg:str, cnt:int, total:int) -> None:
    percent = round(cnt/total, ROUNDING)
    print(f"{msg}: {cnt}/{total} ({percent})")

# - - - Impact and Change sets  - - - #
def get_reductions_per_trial(label:str,
 unreduced_dct:dict[str,list],
 reduced_dct:dict[str,list],
 assertions:bool=True, percent:bool=True) -> list[float]:
    '''
    Returns an array of reductions given two parallel dictionaries which
    map a "dirpath" (a specific trial) to a list of either 
    DependencyFunctionChange or Impacted objects.
    '''
    reductions_per_trial = []
    for dirpath,dirpath_unreduced in zip(reduced_dct,unreduced_dct):

        unreduced_cnt = len(unreduced_dct[dirpath_unreduced])
        reduced_cnt = len(reduced_dct[dirpath])

        if assertions:
            if unreduced_cnt < reduced_cnt:
                print_err(f"Inconsistent data point: {unreduced_cnt} "
                    f"-> {reduced_cnt}: {label} "
                    f"{dirpath_unreduced} -> {dirpath}"
                )
            assert unreduced_cnt >= reduced_cnt

        reductions_per_trial.append(unreduced_cnt - reduced_cnt)
        if percent and unreduced_cnt!=0:
            reductions_per_trial[-1] /= unreduced_cnt

    return reductions_per_trial

@dataclass(init=True)
class Case:
    '''
    Holds descriptive data for each case: libonig, libexpat and libusb
    '''
    total_functions: int
    name: str
    # Color to use for bar plots
    color: str

    # Holds one entry per function that was analyzed (dict key),
    # each item contains an array of AnalysisResult that
    # were encountered for the particular function
    # during full and identity analysis
    function_results_dict: dict[str,FunctionResult]

    # Holds one entry per CSV row across all results, dict key
    # is the path to the CSV file
    cbmc_results_dict: dict[str,list[CbmcResult]]

    # Holds a dict of function names mapped onto a list of 
    # StateParam objects which describe the possible constant values 
    # for each parameter, the outer dict is the path to a specific trial
    arg_states: dict[str,dict[str,list[StateParam]]] =\
            field(default_factory=dict)

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
    def new(cls,name:str, total_functions:int, color:str):
        function_results_dict, cbmc_results_dict = \
            load_cbmc_results(name,OPTIONS.RESULT_DIR)

        base_change_set, reduced_change_set, trans_change_set = \
                load_change_sets(name,OPTIONS.RESULT_DIR)

        _,_,trans_set_without_reduction = \
                load_change_sets(name,OPTIONS.IMPACT_DIR)

        # The number of changed functions in the base set and the functions
        # from cbmc analysis should be equal
        assert len(base_change_set) == len(cbmc_results_dict)

        return cls(name=name,
            total_functions=total_functions,
            cbmc_results_dict=cbmc_results_dict,
            function_results_dict=function_results_dict,
            color=color,

            arg_states = load_state_space(name,OPTIONS.RESULT_DIR),

            base_change_set = base_change_set,
            trans_change_set = trans_change_set,
            impact_set = load_impact_set(name,OPTIONS.RESULT_DIR),

            reduced_change_set = reduced_change_set,
            trans_set_without_reduction = trans_set_without_reduction,
            impact_set_without_reduction = \
                    load_impact_set(name,OPTIONS.IMPACT_DIR)
        )

    def info(self):
        print_stage(self.name)

        # The total number of analyzed functions corresponds to the number of
        # functions that were observed as changed in at least one case,
        # every changed function will generate a CBMC entry even if
        # it cannot be analyzed in `valid_preconds()`
        nr_of_changed_functions = len(self.function_results())

        basic_dist("Changed functions",
            nr_of_changed_functions, self.total_functions
        )
        basic_dist("Passed identity analysis at least once",
            len(self.passed_identity_functions()), nr_of_changed_functions
        )

        #nr_of_full_analysis_results = len(list(filter(lambda c: not c.identity,
        #        self.cbmc_results())))
        #print(f"Unique pre-analysis results: "
        #      f"{len(self.unique_cbmc_results(ident=True))}/"
        #      f"{len(self.cbmc_results())}")
        #print(f"Unique full-analysis results: "
        #      f"{len(self.unique_cbmc_results(ident=False))}/"
        #      f"{nr_of_full_analysis_results}")

        #multi_cnt = len(self.multi_result_function_results())
        #fully_analyzed = self.fully_analyzed_functions()

        #equiv_results = AnalysisResult.results_that_reduce()

        #equiv_result_cnt = len(list(filter(lambda x:
        #    1 <= len(equiv_results|set(x.results)) <= len(equiv_results),
        #    fully_analyzed
        #)))
        #influential_result_cnt = len(list(filter(lambda x:
        #    1 <= len({
        #        AnalysisResult.FAILURE,
        #        AnalysisResult.FAILURE_UNWIND_FAIL
        #        } | set(x.results)) <= 2 ,
        #    fully_analyzed
        #)))

        #print(f"Functions with an influential and equivalent analysis result: "
        #      f"{multi_cnt}/{nr_of_changed_functions}")
        #print(f"Functions with \033[4monly\033[0m equivalent analysis results: "
        #      f"{equiv_result_cnt}/{nr_of_changed_functions}"
        #)
        #print(f"Functions with \033[4monly\033[0m influential analysis results: "
        #      f"{influential_result_cnt}/{nr_of_changed_functions}")

        #dupes = "\033[4mwithout duplicates\033[0m" if unique_results else \
        #    "\033[4mwith duplicates\033[0m"
        #print(f"Result distribution {dupes} (pre-analysis):")
        #pprint(self.sorted_analysis_dist(
        #    ident=True,filter_zero=True,unique_results=unique_results)
        #)
        #print(f"Result distribution {dupes} (full-analysis):")
        #pprint(self.sorted_analysis_dist(
        #    ident=False,filter_zero=True,unique_results=unique_results)
        #)


        print("=======================================")

        change_set_sizes = [ len(v) for v in self.base_change_set.values() ]
        trans_set_sizes = [ len(v) for v in self.trans_change_set.values() ]
        impact_set_sizes = [ len(v) for v in self.impact_set.values() ]

        average_set(change_set_sizes,
            get_reductions_per_trial("Change set",
                self.base_change_set,
                self.reduced_change_set
            ), "change"
        )
        average_set(trans_set_sizes,
            get_reductions_per_trial("Transitive set",
                self.trans_set_without_reduction,
                self.trans_change_set
            ), "transitive"
        )
        average_set(impact_set_sizes,
            get_reductions_per_trial("Impact set",
                self.impact_set_without_reduction,
                self.impact_set
            ), "impact"
        )

    #  - - - FunctionResult  - - - #
    def multi_result_function_results(self,ident:bool=False) \
     -> list[FunctionResult]:
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

    def passed_identity_functions(self) -> list[FunctionResult]:
        '''
        Returns the functions which passed
        the identity comparision at least once.
        This corresponds to every function that has at least one
        full analysis result.
        '''
        funcs_with_at_least_one_valid_id_cmp = list(filter(lambda v:
                len(v.results)>0,
                self.function_results()
        ))
        return funcs_with_at_least_one_valid_id_cmp

    # - - - AnalysisResult distribution - - - - #
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

    def unique_cbmc_results(self,ident:bool) -> set[tuple[str,AnalysisResult]]:
        '''
        Return a set of all encountered (function_name,AnalysisResult) tuples
        in within the CBMC result.
        '''
        return set(map(lambda c: (c.func_name,c.result),
                filter(lambda r: r.identity == ident,
                    self.cbmc_results()
                ))
            )

    def analysis_dist(self,
        ident:bool,
        filter_zero:bool=False,
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
            analysis_result_total_cnt = sum(map(lambda f: len(f.results_id),
                self.function_results()))
        else:
            # Functions which did not pass the identity check will have
            # a results array with len()==0
            analysis_result_total_cnt = sum(map(lambda f: len(f.results),
                self.function_results()))

        filtered_cbmc_results = filter(lambda c: c.identity == ident,
                self.cbmc_results())

        result_cnts = { e.name: 0 for e in AnalysisResult }

        if unique_results:
            # Only increment the result count for unique entries,
            # e.g. count 16 SUCCESS results for a function as 1 SUCCESS
            # This also requires the `analysis_result_total_cnt` to be reduced
            # for percentages to be correct
            unique_cbmc_results = self.unique_cbmc_results(ident=ident)

            for tpl in unique_cbmc_results:
                result_cnts[tpl[1].name] += 1

            analysis_result_total_cnt = len(unique_cbmc_results)
        else:
            for cbmc_result in filtered_cbmc_results:
                result_cnts[cbmc_result.result.name] += 1

        if filter_zero:
            result_cnts = { key: val
                    for key,val in result_cnts.items() if val != 0
            }

        analysis_dict = { AnalysisResult[tpl[0]]: tpl[1]/analysis_result_total_cnt
                for tpl in result_cnts.items() }

        assert (sum(list(analysis_dict.values())) - 1) < 10**-12
        return analysis_dict

    # - - - Helpers - - - #
    def function_results(self) -> list[FunctionResult]:
        return list(self.function_results_dict.values())

    def cbmc_results(self) -> list[CbmcResult]:
        return flatten(list(self.cbmc_results_dict.values()))

    def libname(self) -> str:
        return 'libusb-1.0' if self.name=='libusb' else self.name
    def reponame(self) -> str:
        return 'oniguruma' if self.name=='libonig' else self.name

