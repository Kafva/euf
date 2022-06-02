#!/usr/bin/env python3
import os,sys
from posixpath import expanduser
import matplotlib.pyplot as plt
from matplotlib.figure import Figure

# '.' is needed to run from the visualise directory
sys.path.extend(['..','.'])

# pylint: disable=wrong-import-position
from src.config import CONFIG
from src.types import HarnessType
from src.util import print_info, print_stage
from visualise import OPTIONS
from visualise.plot import correctness_p_value, plot_analysis_dists, plot_reductions, \
        plot_state_space
from visualise.case import Case
from visualise.util import divider, identity_set
from visualise.write_md import write_md, dump_multi_result_csv

def save_figure(path: str, figure:Figure):
    result_dir = os.path.dirname(path)
    if os.path.isdir(result_dir) and OPTIONS.SAVE_FIGS:
        filename = os.path.basename(path)
        if OPTIONS.EXPORT_LIGHT:
            filename = filename.split('.')[0] + "_white."\
                    + filename.split('.')[1]
            path = f"{result_dir}/{filename}"
        figure.savefig(path,
            dpi=OPTIONS.DPI,
            facecolor=OPTIONS.BLACK,
            transparent=True,
            edgecolor=OPTIONS.WHITE
        )

def dir_cnt(path:str):
    return len([ p for p in os.listdir(path) \
            if os.path.isdir(f"{path}/{p}")])

if __name__ == '__main__':
    if not OPTIONS.EXPORT_LIGHT:
        plt.rcParams['text.color'] = OPTIONS.WHITE
        plt.rcParams['axes.labelcolor'] = OPTIONS.WHITE
        plt.rcParams['xtick.color'] = OPTIONS.WHITE
        plt.rcParams['ytick.color'] = OPTIONS.WHITE
        plt.rcParams['axes.edgecolor'] = OPTIONS.WHITE
        plt.rcParams['axes.facecolor'] = OPTIONS.BLACK
        plt.rcParams['savefig.facecolor']= OPTIONS.BLACK
        plt.rcParams['figure.facecolor'] = OPTIONS.BLACK

    total_trials = dir_cnt(OPTIONS.RESULT_DIR)
    print_info(f"Total trials: {total_trials} "
               f"({round(total_trials/3,1)} per project)"
    )

    BASE_PATH = f"{expanduser('~')}/Repos"
    onig = Case.new(name="libonig", git_dir=f"{BASE_PATH}/oniguruma",
            total_functions=1186, color=OPTIONS.RED)
    expat = Case.new(name="libexpat", git_dir=f"{BASE_PATH}/libexpat",
            total_functions=645, color=OPTIONS.GREEN)
    usb = Case.new(name="libusb", git_dir=f"{BASE_PATH}/libusb",
            total_functions=1346, color=OPTIONS.BLUE)

    cases = [onig,expat,usb]

    if OPTIONS.P_VALUES:
        fig = correctness_p_value(OPTIONS.CORRECTNESS_CSV)
        save_figure(f"{OPTIONS.FIGURE_DIR}/confusion_matrix.png", fig)

    # Specify what we consider as a 'multi-result'
    CONFIG.REDUCE_INCOMPLETE_UNWIND = True
    for c in cases:
        c.info()

    divider()

    if OPTIONS.PLOT:
        fig = plot_analysis_dists(cases,harness_types={HarnessType.NONE})
        save_figure(f"{OPTIONS.FIGURE_DIR}/result_dist_precond.png", fig)

        fig = plot_analysis_dists(cases,harness_types=identity_set())
        save_figure(f"{OPTIONS.FIGURE_DIR}/result_dist_id.png", fig)

        fig = plot_analysis_dists(cases,harness_types={HarnessType.STANDARD})
        save_figure(f"{OPTIONS.FIGURE_DIR}/result_dist.png", fig)

        fig = plot_reductions(cases,percent=OPTIONS.REDUCTION_IN_PERCENT)
        save_figure(f"{OPTIONS.FIGURE_DIR}/reduction_violin.png", fig)

        fig = plot_state_space(cases)
        save_figure(f"{OPTIONS.FIGURE_DIR}/states_violin.png", fig)

        plt.subplots_adjust(bottom=0.15)
        plt.xticks(fontsize=OPTIONS.PLOT_FONT_SIZE)
        plt.show()


    if OPTIONS.WRITE_MD:
        write_md(cases, OPTIONS.RESULT_DIR, only_multi=OPTIONS.ONLY_MULTI)
    if OPTIONS.LIST_ANALYZED:
        divider()
        for case in cases:
            print_stage(case.name)
            results = case.multi_result_function_results() \
                    if OPTIONS.ONLY_MULTI \
                    else case.passed_identity_functions()
            for r in results:
                print(r.pretty())
    if OPTIONS.DUMP_MULTI_RESULT_CSV:
        dump_multi_result_csv(cases)

