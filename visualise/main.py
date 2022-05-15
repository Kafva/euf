#!/usr/bin/env python3
import os,sys
import matplotlib.pyplot as plt
from matplotlib.figure import Figure

# '.' is needed to run from the visualise directory
sys.path.extend(['..','.'])

# pylint: disable=wrong-import-position
from src.config import CONFIG
from src.util import print_info, print_stage
from visualise import OPTIONS
from visualise.plot import plot_analysis_dists, plot_reductions, write_report
from visualise.case import Case

def save_figure(path: str, figure:Figure):
    result_dir = os.path.dirname(path)
    if os.path.isdir(result_dir) and OPTIONS.SAVE_FIGS:
        filename = os.path.basename(path)
        if OPTIONS.EXPORT_LIGHT:
            filename = filename.split('.')[0] + "_white."\
                    + filename.split('.')[1]
            path = f"{result_dir}/{filename}"
        figure.savefig(path,
            dpi=900,
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

    onig = Case.new(name="libonig", total_functions=1186, color=OPTIONS.RED)
    expat = Case.new(name="libexpat",total_functions=645,color=OPTIONS.GREEN)
    usb = Case.new(name="libusb", total_functions=1346,color=OPTIONS.BLUE)

    cases = [onig,expat,usb]

    CONFIG.RESULTS_DIR = OPTIONS.RESULT_DIR

    if OPTIONS.PLOT:
        fig = plot_analysis_dists(cases,ident=True)
        save_figure(f"{OPTIONS.FIGURE_DIR}/result_dist_id.png", fig)

        fig = plot_analysis_dists(cases,ident=False)
        save_figure(f"{OPTIONS.FIGURE_DIR}/result_dist.png", fig)

        fig = plot_reductions(cases,percent=False)
        save_figure(f"{OPTIONS.FIGURE_DIR}/reduction_violin.png", fig)

        plt.subplots_adjust(bottom=0.15)
        plt.xticks(fontsize=OPTIONS.PLOT_FONT_SIZE)
        plt.show()

    # Specify what we consider as a 'multi-result'
    CONFIG.REDUCE_INCOMPLETE_UNWIND = True
    print_info(f"REDUCE_INCOMPLETE_UNWIND: "
        f"{CONFIG.REDUCE_INCOMPLETE_UNWIND}\n"
    )
    for c in cases:
        c.info()

    if OPTIONS.WRITE_MD:
        write_report(cases,only_multi=OPTIONS.ONLY_MULTI)
    if OPTIONS.LIST_ANALYZED:
        print("\n=============================")
        for case in cases:
            print_stage(case.name)
            results = case.multi_result_function_results() \
                    if OPTIONS.ONLY_MULTI \
                    else case.fully_analyzed_functions()
            for r in results:
                print(r.pretty())
