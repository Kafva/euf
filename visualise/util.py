import os
from statistics import mean, stdev
from src.types import HarnessType, StateParam

from src.util import print_err
from visualise import ROUNDING

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

def get_constrained_functions(
 func_arg_states: dict[str,dict[str,tuple[StateParam,float]]]) -> \
 tuple[dict[str,float],dict[str,list[str]]]:
    '''
    Returns two dictionaries: 
        { func_name: average_percent_constrained_params } 
        { fully_constrained_func: [dirpaths] }
    '''
    fully_constrained_funcs = {}
    constrained_percent_mean_per_func = { f: .0 for f in func_arg_states }
    for func_name, dirpath_dict in func_arg_states.items():
        constrained_percent_mean_per_func[func_name] = \
            sum(map(lambda tpl: tpl[1], dirpath_dict.values())) / len(dirpath_dict)

        for dirpath, tpl in dirpath_dict.items():
            if tpl[1] == 1.0:
                if func_name not in fully_constrained_funcs:
                    fully_constrained_funcs[func_name] = [ dirpath ]
                else:
                    fully_constrained_funcs[func_name].append(dirpath)

    return constrained_percent_mean_per_func, fully_constrained_funcs

