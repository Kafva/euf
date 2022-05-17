import os, json
from dataclasses import dataclass
from visualise.types import CbmcResult, FunctionResult, StateFailResult
from src.types import StateParam, DependencyFunctionChange

@dataclass(init=True)
class Impacted:
    main_project_fn_name:str
    dependecy_fn_name:str

def load_change_set(dirpath:str,filename:str,
 change_set:dict[str,list[DependencyFunctionChange]]) -> None:
    if os.path.isfile(f"{dirpath}/{filename}"):
        with open(f"{dirpath}/{filename}", mode='r', encoding='utf8') as f:
            for line in f.readlines()[1:]:
                change_set[dirpath].append(DependencyFunctionChange.\
                        new_from_change_set_csv(line.split(";"))
                )

def load_change_sets(name:str, results_dir:str) -> \
 tuple[\
 dict[str,list[DependencyFunctionChange]],\
 dict[str,list[DependencyFunctionChange]],\
 dict[str,list[DependencyFunctionChange]]\
 ]:
    base_change_set = {}
    reduced_change_set = {}
    trans_change_set = {}
    for item in os.listdir(results_dir):
        dirpath = f"{results_dir}/{item}"
        # Only load entries matching the current name
        if os.path.isdir(dirpath) and item.startswith(name):
            base_change_set[dirpath] = []
            reduced_change_set[dirpath] = []
            trans_change_set[dirpath] = []

            load_change_set(dirpath, "change_set.csv",
                    base_change_set)
            load_change_set(dirpath, "reduced_set.csv",
                    reduced_change_set)
            load_change_set(dirpath, "trans_change_set.csv",
                    trans_change_set)

    return base_change_set, reduced_change_set, trans_change_set

def load_impact_set(name:str, results_dir:str) -> dict[str,list[Impacted]]:
    impact_set = {}
    for item in os.listdir(results_dir):
        dirpath = f"{results_dir}/{item}"

        # Only load entries matching the current name
        if os.path.isdir(dirpath) and item.startswith(name):
            impact_set[dirpath] = []

            if os.path.isfile(f"{dirpath}/impact_set.csv"):
                with open(f"{dirpath}/impact_set.csv",
                  mode = 'r', encoding='utf8') as f:
                    for line in f.readlines()[1:]:
                        csv_values = line.split(";")
                        impact_set[dirpath].append(Impacted(
                            main_project_fn_name=csv_values[3],
                            dependecy_fn_name=csv_values[8]
                        ))
    return impact_set

def load_state_space(name:str, results_dir:str) -> dict[str,dict[str,list[StateParam]]]:
    arg_states = {}
    for item in os.listdir(results_dir):
        dirpath = f"{results_dir}/{item}"
        arg_states[dirpath] = {}

        # Only load entries matching the current name
        if os.path.isdir(dirpath) and item.startswith(name):

            if os.path.isfile(f"{dirpath}/states.json"):
                with open(f"{dirpath}/states.json", mode = 'r', encoding='utf8') as f:
                    dct = json.load(f)
                    for func_name in dct:
                        param_states = []
                        for i,param in \
                           enumerate(dct[func_name]['parameters']):
                            param_states.append(
                                StateParam.new_from_dct(param,i)
                            )
                        arg_states[dirpath][func_name] = param_states
    return arg_states

def load_failed_state_analysis(name:str, results_dir:str) -> \
 dict[str,list[StateFailResult]]:
    '''
    The state_fail.csv format only has two columns, 'subdir;symbol_name'.
    '''
    state_fails = {}
    for item in os.listdir(results_dir):
        dirpath = f"{results_dir}/{item}"
        state_fails[dirpath] = []

        # Only load entries matching the current name
        if os.path.isdir(dirpath) and item.startswith(name):

            if os.path.isfile(f"{dirpath}/state_fail.csv"):
                with open(f"{dirpath}/state_fail.csv", mode = 'r', encoding='utf8') as f:
                    for line in f.readlines()[1:]:
                        state_fails[dirpath].append(
                            StateFailResult.new_from_csv(line)
                        )
    return state_fails

def load_cbmc_results(name:str, result_dir:str) -> \
 dict[str,FunctionResult]:
    '''
    Load the data from every cbmc.csv for a given case (libonig etc.)
    under the given result_dir.
    '''
    function_results_dict = {}

    for item in os.listdir(result_dir):
        dirpath = f"{result_dir}/{item}"

        # Only load entries matching the current name
        if os.path.isdir(dirpath) and item.startswith(name):
            cbmc_results = load_cbmc_result(
                    dirpath,
                    function_results_dict
            )

            # Add each row from each cbmc.csv to a FunctionResult
            # object, effectively mapping each function name to a set of rows.
            for cbmc_result in cbmc_results:
                if cbmc_result.func_name in function_results_dict:
                    function_results_dict[cbmc_result.func_name].cbmc_results\
                            .append(cbmc_result)
                else:
                    function_results_dict[cbmc_result.func_name] =\
                            [ cbmc_result ]

    return function_results_dict

def load_cbmc_result(dirpath:str, \
  function_results_dict: dict[str,FunctionResult]) -> list[CbmcResult]:
    '''
    Load each row of cbmc.csv from the provided dirpath into a list
    of CbmcResult objects and populate the provided dict with
    FunctionResults.
    '''
    cbmc_results = []

    if os.path.isfile(f"{dirpath}/cbmc.csv"):
        with open(f"{dirpath}/cbmc.csv", mode = 'r', encoding='utf8') as f:
            for line in f.readlines()[1:]:
                cbmc_results.append(
                    CbmcResult.new(line.split(";"), dirpath)
                )

                # Add a key for each encountered function name
                func_name = cbmc_results[-1].func_name
                if func_name not in function_results_dict:
                    function_results_dict[func_name] =\
                        FunctionResult(func_name=func_name)

    return cbmc_results
