import os, json
from dataclasses import dataclass
from src.types import DependencyFunctionChange, StateParam

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
