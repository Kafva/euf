from pprint import pprint
from dataclasses import dataclass, field
from statistics import mean, stdev
from src.config import CONFIG
from src.types import AnalysisResult, \
        DependencyFunctionChange, HarnessType, StateParam
from src.util import flatten, print_info, print_stage
from visualise import OPTIONS, ROUNDING

from visualise.deserialise import Impacted, \
    load_change_sets, load_failed_state_analysis, load_impact_set, \
    load_state_space, load_cbmc_results
from visualise.types import CbmcResult, FunctionResult, StateFailResult
from visualise.util import average_set, basic_dist, divider, get_constrained_functions, \
        get_reductions_per_trial, identity_set

@dataclass(init=True)
class Case:
    '''
    Holds descriptive data for each case: libonig, libexpat and libusb
    '''
    total_functions: int
    name: str
    git_dir:str
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
    arg_states_dict: dict[str,dict[str,list[StateParam]]] =\
            field(default_factory=dict)

    # A mapping from each trial of state space anaylsis
    # instances which failed onto a tuple list on the form
    #       (subdir, func_name)
    state_fails_dict: dict[str,list[StateFailResult]] =\
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
    def new(cls,name:str, git_dir:str, total_functions:int, color:str):
        function_results_dict = load_cbmc_results(name,OPTIONS.RESULT_DIR)

        base_change_set, reduced_change_set, trans_change_set = \
                load_change_sets(name,OPTIONS.RESULT_DIR)

        _,_,trans_set_without_reduction = \
                load_change_sets(name,OPTIONS.IMPACT_DIR)



        return cls(name=name,git_dir=git_dir,
            total_functions=total_functions,
            function_results_dict=function_results_dict,
            color=color,

            arg_states_dict = load_state_space(name,OPTIONS.RESULT_DIR),

            base_change_set = base_change_set,
            trans_change_set = trans_change_set,
            impact_set = load_impact_set(name,OPTIONS.RESULT_DIR),

            reduced_change_set = reduced_change_set,
            trans_set_without_reduction = trans_set_without_reduction,
            impact_set_without_reduction = \
                    load_impact_set(name,OPTIONS.IMPACT_DIR),
            state_fails_dict = load_failed_state_analysis(name, OPTIONS.RESULT_DIR)
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
        print_info("Divided by the combined number of cbmc.csv rows")

        cbmc_results_cnt = len(self.cbmc_results())

        basic_dist("Unique NONE harness results",
            len(self.unique_results({HarnessType.NONE})),
            cbmc_results_cnt
        )
        unique_identity_results = self.unique_results(identity_set())
        basic_dist("Unique IDENTITY harness results",
            len(unique_identity_results),
            cbmc_results_cnt
        )
        basic_dist("Unique STANDARD harness results",
            len(self.unique_results({HarnessType.STANDARD})),
            cbmc_results_cnt
        )

        divider()
        print_info("Divided by the number of functions that passed identity "\
                "verification at least once")

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
              f"{multi_cnt}/{len(unique_identity_results)}")
        print(f"Functions with \033[4monly\033[0m equivalent analysis results: "
              f"{equiv_result_cnt}/{len(unique_identity_results)}"
        )
        print(f"Functions with \033[4monly\033[0m influential analysis results:"
              f" {influential_result_cnt}/{len(unique_identity_results)}")

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

        divider()

        func_arg_states = self.arg_states()

        basic_dist("Harnesses with at least one assumption",
              len(func_arg_states), len(unique_identity_results)
        )

        constrained_percent_mean_per_func, fully_constrained_funcs = \
                get_constrained_functions(func_arg_states)

        if len(constrained_percent_mean_per_func) >= 2:
            m = round(mean(constrained_percent_mean_per_func.values()),ROUNDING)
            s = round(stdev(constrained_percent_mean_per_func.values()),ROUNDING)
        else:
            m=s=0

        print(f"Percentage of constrained parameters per constrained function: {m} (±{s})")
        print(f"Fully constrained harnesses: {len(fully_constrained_funcs)}")
        if len(fully_constrained_funcs)>0:
            for func_name,dirpaths in fully_constrained_funcs.items():
                print(f"{CONFIG.INDENT}\033[33m{func_name}\033[0m: ", dirpaths)

        per_func_fail_cnt, total_fails = self.get_per_func_fails()

        print(f"Failed state space anaylsis: ({total_fails} in total)")
        for func_name,cnt in per_func_fail_cnt.items():
            print(f"{CONFIG.INDENT}\033[31m{func_name}\033[0m: {cnt}")

    # - - - State space  - - - #
    def arg_states(self) -> dict[str,dict[str,tuple[StateParam,float]]]:
        '''
        The internal arg_states_dict maps every trial to a set of
        (func_name,StateParam) tuples that describe the possible states for
        a function. This wrapper flattens the datastructure to a new format
        {
            function_name: {
                dirpath1: ([StateParams], constrained_percent),
                dirpath2: ([StateParams], constrained_percent) ,
            }
        }
        where each function is the outer key and maps onto a list of encountered
        StateParam sets for it. We keep the dirpath as a key to enable back
        correlation with the actual harness that attained a specific set of
        params.
        '''
        arg_states_with_fnc_key = {}
        for dirpath,arg_states_for_dir in self.arg_states_dict.items():
            for func_name,states in arg_states_for_dir.items():

                # Skip all unconstrained functions
                if len(states)==0:
                    continue

                if func_name not in arg_states_with_fnc_key:
                    arg_states_with_fnc_key[func_name] = {}

                constrained_param_cnt = len([
                    s for s in states if not s.nondet
                ])

                arg_states_with_fnc_key[func_name][dirpath] = (
                    states,
                    constrained_param_cnt/len(states)
                )

        return arg_states_with_fnc_key

    def get_per_func_fails(self) -> tuple[dict[str,int],int]:
        per_func_fail_cnt = {}
        total_fails = 0
        for state_fail_li in self.state_fails_dict.values():
            for state_fail in state_fail_li:
                if state_fail.func_name not in per_func_fail_cnt:
                    per_func_fail_cnt[state_fail.func_name] = 1
                else:
                    per_func_fail_cnt[state_fail.func_name] += 1
                total_fails+=1
        return per_func_fail_cnt, total_fails

    # - - - FunctionResult  - - - #
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

