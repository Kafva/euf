import os
from pprint import pprint
from statistics import stdev,mean
from dataclasses import dataclass, field
from src.types import AnalysisResult, \
        DependencyFunctionChange, HarnessType, StateParam
from src.util import flatten, print_err, print_stage
from visualise import OPTIONS

from visualise.deserialise import Impacted, \
    load_change_sets, load_impact_set, load_state_space, load_cbmc_results
from visualise.types import CbmcResult, FunctionResult

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

def divider(percent:float=1.0) -> None:
    print("="*int(os.get_terminal_size().columns*percent))

def identity_set() -> set[HarnessType]:
    return {HarnessType.IDENTITY_OLD, HarnessType.IDENTITY}

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
        function_results_dict = load_cbmc_results(name,OPTIONS.RESULT_DIR)

        base_change_set, reduced_change_set, trans_change_set = \
                load_change_sets(name,OPTIONS.RESULT_DIR)

        _,_,trans_set_without_reduction = \
                load_change_sets(name,OPTIONS.IMPACT_DIR)

        return cls(name=name,
            total_functions=total_functions,
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

        divider()

        cbmc_results_cnt = len(self.cbmc_results())
        print(f"Unique NONE harness results: "
              f"{len(self.unique_results({HarnessType.NONE}))}/"
              f"{cbmc_results_cnt}")
        print(f"Unique IDENTITY harness results: "
              f"{len(self.unique_results(identity_set()))}/"
              f"{cbmc_results_cnt}")
        print(f"Unique STANDARD harness results: "
              f"{len(self.unique_results({HarnessType.STANDARD}))}/"
              f"{cbmc_results_cnt}")

        divider()

        multi_cnt = len(self.multi_result_function_results())
        passed_identity_results = self.passed_identity_functions()
        equiv_results = AnalysisResult.results_that_reduce()

        equiv_result_cnt = len(list(filter(lambda x:
            1 <= len(equiv_results|set(x.results())) <= len(equiv_results),
            passed_identity_results
        )))
        influential_result_cnt = len(list(filter(lambda x:
            1 <= len({
                AnalysisResult.FAILURE,
                AnalysisResult.FAILURE_UNWIND_FAIL
                } | set(x.results())) <= 2 ,
            passed_identity_results
        )))

        print(f"Functions with an influential and equivalent analysis result: "
              f"{multi_cnt}/{nr_of_changed_functions}")
        print(f"Functions with \033[4monly\033[0m equivalent analysis results: "
              f"{equiv_result_cnt}/{nr_of_changed_functions}"
        )
        print(f"Functions with \033[4monly\033[0m influential analysis results:"
              f" {influential_result_cnt}/{nr_of_changed_functions}")

        divider()

        dupes = "\033[4mwithout duplicates\033[0m" \
            if OPTIONS.UNIQUE_ONLY else \
            "\033[4mwith duplicates\033[0m"

        print(f"(NONE) Result distribution {dupes}:")
        pprint(self.sorted_analysis_dist(
            harness_types={HarnessType.NONE},
            filter_zero=True, unique_only=OPTIONS.UNIQUE_ONLY
        ))

        print(f"(IDENTITY) Result distribution {dupes}:")
        pprint(self.sorted_analysis_dist(
            harness_types=identity_set(),
            filter_zero=True, unique_only=OPTIONS.UNIQUE_ONLY
        ))
        print(f"(STANDARD) Result distribution {dupes}:")
        pprint(self.sorted_analysis_dist(
            harness_types={HarnessType.STANDARD},
            filter_zero=True, unique_only=OPTIONS.UNIQUE_ONLY
        ))

        divider()
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
    def multi_result_function_results(self,identity:bool=False) \
     -> list[FunctionResult]:
        multi_results = []
        for func_res in self.function_results():
            if func_res.has_multi_result(identity):
                multi_results.append(func_res)
        return multi_results

    def passed_identity_functions(self) -> list[FunctionResult]:
        '''
        Returns the functions which passed
        the identity comparision at least once.
        This corresponds to every function that has at least one
        full analysis result.
        '''
        funcs_with_at_least_one_valid_id_cmp = list(filter(lambda v:
                len(v.results())>0,
                self.function_results()
        ))
        return funcs_with_at_least_one_valid_id_cmp

    # - - - AnalysisResult distribution - - - - #
    def sorted_analysis_dist(self,harness_types: set[HarnessType],
      filter_zero:bool,unique_only:bool):
        li = [ (key.name,round(val,ROUNDING)) for key,val in
                self.analysis_dist(
                    harness_types=harness_types,
                    filter_zero=filter_zero,
                    unique_only=unique_only
                ).items()
        ]
        return sorted(li, key=lambda l: l[1], reverse=True)

    def unique_results(self, harness_types:set[HarnessType]) \
     -> set[tuple[str,AnalysisResult]]:
        '''
        Return a set of all encountered (function_name,AnalysisResult) tuples
        within the CBMC result which are of one of the given types.
        Note that a single CbmcResult can have more than one outcome.
        '''
        tpls = set()

        for c in self.cbmc_results():
            if c.harness_type in harness_types:
                for r in c.result:
                    tpls.add((c.func_name,r))

        return tpls

    def analysis_dist(self, harness_types: set[HarnessType],
     filter_zero:bool=False, unique_only:bool=False) \
     -> dict[AnalysisResult,float]:
        '''
        Returns a dict of percentages for each AnalysisResult
        across every function analysis (during either the precondition,
        identity or final stage).
        '''

        # Calculate the total number of analysis results for the relevant type
        #
        # For the IDENTITY and STANDARD cases we have an equal number of
        # of function analysis tries and corresponding AnalysisResult objects
        #
        # For the NONE case, a single function analysis can give 1 or more
        # AnalysisResult objects. We consider the total number of cases
        # for NONE results as the total number of cbmc.csv entries
        # of this type.
        #
        # Dividing by this number means that the percentages for the NONE
        # cases will _not_ add up to 1. E.g. 70% of functions may have
        # a void return value while 60% could have had a changed return value
        if len(harness_types & {HarnessType.NONE}) == 1:
            analysis_results = flatten(
                [ f.results_none() for f in self.function_results() ]
            )
            analysis_result_total_cnt = len(
                [c for c in self.cbmc_results() if \
                    c.harness_type==HarnessType.NONE ]
            )

        elif len(harness_types & identity_set()) >= 1:
            analysis_results = flatten(
                [ f.results_id() for f in self.function_results() ]
            )
            analysis_result_total_cnt = len(analysis_results)

        elif len(harness_types & {HarnessType.STANDARD}) == 1:
            analysis_results = flatten(
                [ f.results() for f in self.function_results() ]
            )
            analysis_result_total_cnt = len(analysis_results)
        else:
            raise Exception("Invalid HarnessType set")

        result_cnts = { e.name: 0 for e in AnalysisResult }

        if unique_only:
            # Only increment the result count for unique entries,
            # e.g. count 16 SUCCESS results for a function as 1 SUCCESS
            #
            # This also requires the `analysis_result_total_cnt` to be reduced
            # for percentages to be correct
            unique_results = self.unique_results(harness_types)

            for tpl in unique_results:
                result_cnts[tpl[1].name] += 1

            analysis_result_total_cnt = len(unique_results)
        else:
            for analysis_result in analysis_results:
                result_cnts[analysis_result.name] += 1

        if filter_zero:
            result_cnts = { key: val
                    for key,val in result_cnts.items() if val != 0
            }

        analysis_dict = { AnalysisResult[tpl[0]]:
                    tpl[1]/analysis_result_total_cnt if
                    analysis_result_total_cnt != 0 else \
                    tpl[1]
                for tpl in result_cnts.items() }

        if HarnessType.NONE not in harness_types:
            assert (sum(list(analysis_dict.values())) - 1) < 10**-12
        return analysis_dict

    # - - - Helpers - - - #
    def function_results(self) -> list[FunctionResult]:
        return list(self.function_results_dict.values())

    def cbmc_results(self) -> list[CbmcResult]:
        all_results = []
        for f in self.function_results_dict.values():
            all_results.extend(f.cbmc_results)
        return all_results

    def libname(self) -> str:
        return 'libusb-1.0' if self.name=='libusb' else self.name
    def reponame(self) -> str:
        return 'oniguruma' if self.name=='libonig' else self.name

