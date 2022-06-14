import os, re
from statistics import mean, stdev
from textwrap import wrap
from itertools import compress, zip_longest

import matplotlib.pyplot as plt
from matplotlib.figure import Figure
from matplotlib import cm
from sklearn.metrics._plot.confusion_matrix import \
        ConfusionMatrixDisplay, confusion_matrix
from scipy.stats import binomtest

from src.types import AnalysisResult, HarnessType
from src.util import flatten, print_fail, print_info, print_success
from visualise.case import Case
from visualise.util import average_set, get_constrained_functions, \
        get_reductions_per_trial, identity_set, list_to_csv
from visualise import OPTIONS, ROUNDING

def violin_styling(parts):
    cmap = cm.get_cmap(OPTIONS.COLORMAP)

    for pc in parts['bodies']:
        pc.set_facecolor(cmap(0.4))
        pc.set_edgecolor('white')
        pc.set_alpha(0.5)

    # Change colors of the mean indicators
    for partname in ('cbars','cmins','cmaxes','cmeans'):
        vp = parts[partname]
        vp.set_edgecolor(OPTIONS.DARK_PINK)
        vp.set_linewidth(2)

def plot_analysis_dists(cases: list[Case],harness_types: set[HarnessType]) \
  -> Figure:
    '''
    Not using the `unique_only` option gives the impression that expat has
    very good performance, which stems from the fact that it has analyzed
    the same few functions successfully many times.
    '''
    fig = plt.figure(figsize=OPTIONS.FIG_SIZE)
    subfig = fig.subfigures(nrows=1, ncols=1)

    def create_row(title:str,ylabel:str,index:int,unique_only:bool,
     make_plot:bool=True):
        if make_plot:
            subfig.suptitle(title,fontweight='bold',
                    horizontalalignment='center',
                    fontsize=OPTIONS.TITLE_SIZE
            )
            axes = subfig.subplots(nrows=1, ncols=1)
            axes.set_ylabel(ylabel, fontsize=OPTIONS.AXES_SIZE)
            axes.set_xlabel("",fontsize = OPTIONS.AXES_SIZE)

        cases_dists = [ c.analysis_dist(
                            harness_types=harness_types,
                            unique_only=unique_only
                        ).values() for c in cases ]

        non_zero_fields = [ a!=0 or b!=0 or c!=0 for a,b,c in
                zip(cases_dists[0],
                    cases_dists[1],
                    cases_dists[2]) ]

        # Remove fields that are zero across all cases
        cases_dists = [ list(compress(c,non_zero_fields)) for c in cases_dists ]

        bar_names = [ e.name for e in AnalysisResult ]
        bar_names  = list(compress(bar_names, non_zero_fields))


        #== Dump CSV ==#
        def dump_csv(filename):
            if not os.path.isdir(OPTIONS.CSV_DIR):
                os.mkdir(OPTIONS.CSV_DIR)

            filepath = f"{OPTIONS.CSV_DIR}/{filename}" if unique_only \
                    else f"{OPTIONS.CSV_DIR}/dupes_{filename}"

            with open(filepath,
                    mode='w', encoding='utf8') as f:
                f.write(f"{OPTIONS.CSV_LIB_STR};"+list_to_csv(bar_names)+"\n")
                for i,case_dist in enumerate(cases_dists):
                    f.write(
                        f"{cases[i].name};"+
                        list_to_csv(list(
                            map(str,map(lambda x: round(x,ROUNDING),case_dist))
                        )) +
                        "\n"
                    )

        if len(harness_types & {HarnessType.NONE}) == 1:
            dump_csv("precond_dists.csv")
        elif len(harness_types & identity_set()) >= 1:
            dump_csv("id_dists.csv")
        else:
            dump_csv("standard_dists.csv")

        if not make_plot:
            return

        # Wrap the bar name text to X chars
        bar_names_nl = [ '\n'.join(wrap(l, OPTIONS.PLOT_WRAP_CHARS))
                for l in bar_names ]

        # Color-code a bar plot for each case
        for i,case in enumerate(cases):
            # The bottom value must be correctly set to the sum of the previous
            # bars, otherwise overlaps will occur
            match i:
                case 1: bottom = cases_dists[0]
                case 2: bottom = [ x+y for x,y in \
                        zip(cases_dists[0],cases_dists[1]) ]
                case _: bottom = 0

            axes.bar(bar_names_nl, cases_dists[i],# type: ignore
                    width = OPTIONS.PLOT_WIDTH,
                    label = case.name,
                    color = [ case.color ],
                    bottom = bottom,
                    alpha = .7,
                    #edgecolor='white'
            )

        if index==0:
            axes.legend(loc='upper left') # type: ignore


    if len(harness_types & {HarnessType.NONE}) == 1:
        #title = "Invalid preconditions observed amongst changed functions"
        ylabel="Changed functions [%]"
    elif len(harness_types & identity_set()) >= 1:
        #title = "Distribution of CBMC results during identity verification"
        ylabel="Functions with valid preconditions [%]"
    else:
        #title = "Distribution of CBMC results during standard verification"
        ylabel="Functions which passed identity "\
                "verification [%]"

    #create_row(title + " (with duplicates)",ylabel,0,unique_only=False)
    #create_row("Without duplicates",ylabel,1,unique_only=True)
    #create_row(title+" (without duplicates)",ylabel,0,unique_only=True)
    create_row("",ylabel,0,unique_only=True)
    create_row("",ylabel,0,unique_only=False,make_plot=False)

    return fig

def correctness_p_value(filepath: str) -> Figure:
    '''
    Uses trust.csv (produced from "dump_multi_result_csv") as input to derive
    the statistical significance of the correctness analysis.

    Confusion matrix:
                        |EUF equivalent  |EUF influential
    manual equivalent   |TN              |FP
    manual influential  |FN              |TP

    == Mcnemar test ==
    In McNemar's Test, we formulate the null hypothesis that the probabilities
    p(b) and p(c) are the same, or in simplified terms:
    None of the two models performs better than the other.

        H0:
            P(FN) == P(FP)
        H1: P(FN) != P(FP)

    This is not well suited for comparing EUF against the base-classification.

    We instead consider each classification as a Berrnouli experiment:
        0: TP or TN
        1: FP or FN
    and utilise the hypothesis :
        H0: pr <=  MINIMUM_ACCURACY
        H1: pr >   MINIMUM_ACCURACY
    '''
    if not os.path.isfile(filepath):
        raise Exception(f"Not found {filepath}")

    manual_classification = []
    euf_classification = []
    with open(filepath, mode='r', encoding='utf8') as f:
        for line in f.readlines()[1:]:
            # "library;function;infCount;equivCount;influential;equivalent
            # True == influential
            # False == equivalent

            match line.split(';')[4]:
                # TP => influential=sound
                # FP => influential=unsound
                case 'sound':
                    manual_classification.append(True)
                    euf_classification.append(True)
                case 'unsound':
                    manual_classification.append(False)
                    euf_classification.append(True)

            match line.split(';')[5].strip():
                # TN => equivalent=sound
                # FN => equivalent=unsound
                case 'sound':
                    manual_classification.append(False)
                    euf_classification.append(False)
                case 'unsound':
                    manual_classification.append(True)
                    euf_classification.append(False)

    cnf_matrix = confusion_matrix(manual_classification, euf_classification)

    cmatrix = ConfusionMatrixDisplay(cnf_matrix,
        display_labels=["equivalent","influential"],
    )

    cmatrix.plot(cmap=OPTIONS.COLORMAP) # Set a color map
    cmatrix.ax_.set(
        xlabel='EUF classification',
        ylabel='Manual classification',
    )

    correct_classifications = [ True for m,e in \
        zip_longest(manual_classification,euf_classification)
        if m==e
    ]

    #== Conclusion validity ==#
    r = binomtest(
        k = len(correct_classifications),
        n = len(euf_classification),
        p = OPTIONS.DESIRED_ACCURACY,
        alternative='greater'
    )
    pval = r.pvalue # type: ignore
    print_info(f"P-value: {pval}")
    if r.pvalue > OPTIONS.ALPHA:
        print_fail("There is not a statistically significant chance that "
            f"EUF has an accuracy above or equal to {OPTIONS.DESIRED_ACCURACY} "
        )
    else:
        print_success("There is a statistically significant chance that "
            f"EUF has an accuracy above or equal to {OPTIONS.DESIRED_ACCURACY}"
        )

    #== Descriptive stats ==#
    recall = round(
        cnf_matrix[1,1] / (cnf_matrix[1,1]+cnf_matrix[1,0]),
        ROUNDING
    )
    print_info(f"Recall: {recall}")

    precision = round(
        cnf_matrix[1,1] / (cnf_matrix[1,1]+cnf_matrix[0,1]),
        ROUNDING
    )
    print_info(f"Precision: {precision}")

    specificity = round(
        cnf_matrix[0,0] / (cnf_matrix[0,0]+cnf_matrix[0,1]),
        ROUNDING
    )
    print_info(f"Specificity: {specificity}")

    accuracy = round(
        (cnf_matrix[0,0]+cnf_matrix[1,1]) / \
        (cnf_matrix[0,0]+cnf_matrix[0,1]+cnf_matrix[1,0]+cnf_matrix[1,1]),
        ROUNDING
    )
    print_info(f"Accuracy: {accuracy}")

    return cmatrix.figure_

def descriptive_stats(cases: list[Case], percent:bool=False):
    '''
    Call .info() for each case and create CSV files with the corresponding
    information.
    '''
    change_set_sizes = []
    trans_set_sizes = []
    impact_set_sizes = []

    for c in cases:
        change_set_sizes.extend([ len(v) for v in c.base_change_set.values() ])
        trans_set_sizes.extend([ len(v) for v in c.trans_change_set.values() ])
        impact_set_sizes.extend([ len(v) for v in c.impact_set.values() ])


    reductions = flatten([ get_reductions_per_trial("Change set",
        c.base_change_set, c.reduced_change_set, percent=percent
    ) for c in cases ])
    trans_reductions = flatten([ get_reductions_per_trial("Transitive set",
        c.trans_set_without_reduction, c.trans_change_set, percent=percent
    ) for c in cases ])
    impact_reductions = flatten([ get_reductions_per_trial("Impact set",
        c.impact_set_without_reduction, c.impact_set, percent=percent
    ) for c in cases ])

    csv_data_arr = []

    for c in cases:
        csv_data_arr.append(c.info(percent=percent,make_csv=True))

    # Derive the average across all cases
    filepath = f"{OPTIONS.CSV_DIR}/percent_reduction_stats.csv" if \
        percent else f"{OPTIONS.CSV_DIR}/reduction_stats.csv"

    with open(filepath, mode='a', encoding='utf8') as f:
        col1 = list_to_csv(average_set(change_set_sizes, reductions, ""))
        col2 = list_to_csv(average_set(trans_set_sizes, trans_reductions, ""))
        col3 = list_to_csv(average_set(impact_set_sizes, impact_reductions,""))
        f.write(f"\\Sigma;{col1};{col2};{col3}\n")

    # Append the AVERAGE and STDEV for each column of data written to using the csv_data
    # variable in Case.info().
    with open(f"{OPTIONS.CSV_DIR}/analysis_stats.csv", mode='a', encoding='utf8') as f:
        # The CSV data array holds strings on the form 'a/b (c)', we need to
        # extract a and b from each entry and pass the quotient to average_set()

        # Each column is given a 3 item array of quotients
        quotients = [ [.0,.0,.0] for _ in range(len(csv_data_arr[0])) ]
        for j,csv_data in enumerate(csv_data_arr):
            for i,field in enumerate(csv_data):
                a = int(
                    re.search(r"^[0-9]+", field)[0] # type: ignore
                )
                b = int(
                    re.search(r"/[0-9]+", field)[0][1:] # type: ignore
                )
                quotients[i][j] = a/b

        average_set_strs = []
        for q in quotients:
            a = round(mean(q),ROUNDING)
            s = round(stdev(q),ROUNDING)

            average_set_strs.append(f"{a} \\pm{s}")


        f.write(f"\\Sigma;{list_to_csv(average_set_strs)}\n")

def plot_reductions(cases: list[Case],percent:bool=True, stage:int=0) -> Figure:
    '''
    We want to show the average reduction, stdev from the average and the
    extreme values, a violin plot is somewhat suitable for this
    '''
    match stage:
        case 0:
            reductions = [ get_reductions_per_trial("Change set",
                c.base_change_set, c.reduced_change_set, percent=percent
            ) for c in cases ]
        case 1:
            reductions = [ get_reductions_per_trial("Transitive set",
                c.trans_set_without_reduction, c.trans_change_set, percent=percent
            ) for c in cases ]
        case 2:
            reductions = [ get_reductions_per_trial("Impact set",
                c.impact_set_without_reduction, c.impact_set, percent=percent
            ) for c in cases ]


    fig = plt.figure(figsize=OPTIONS.FIG_SIZE)

    def create_row(title:str,index:int,arr:list,label:str):
        title=""#!!
        fig.suptitle(title,
            fontweight='bold',
            horizontalalignment='center',
            fontsize=OPTIONS.MULTI_ROW_TITLE_SIZE
        )
        axes = fig.subplots(nrows=1, ncols=3,
            gridspec_kw = { 'top': 0.4, } # height
        )
        unit = '%' if percent else '#'
        axes[0].set_ylabel(f"Items removed from {label} set [{unit}]",
            fontsize=OPTIONS.REDUCTION_AXES_SIZE,
        )

        for i, ax in enumerate(axes):
            parts = ax.violinplot(
                arr[i],
                showmeans=True, showextrema=True
            )
            violin_styling(parts)
            if index==2:
                ax.set_xlabel("", #cases[i].name,
                    fontweight='normal',
                    fontsize=OPTIONS.REDUCTION_AXES_SIZE,
                    horizontalalignment='center',
                )

            if percent and len(OPTIONS.VIOLIN_YLIM)!=0:
                ax.set_ylim(OPTIONS.VIOLIN_YLIM)

    match stage:
        case 0:
            create_row("Base change set reduction", 0, reductions,# type: ignore
                "change"
            )
        case 1:
            create_row("Transitive change set reduction", 1,
                reductions,# type: ignore
                "transitive"
            )
        case 2:
            create_row("Impact set reduction", 2, reductions,# type: ignore
                "impact"
            )

    return fig

def plot_state_space(cases: list[Case]) -> Figure:
    '''
    Plotting the constrained percentage of functions per case
    is not useful (it would be single bar), this information is better
    given in a plain table.
    '''
    fig = plt.figure(figsize=OPTIONS.FIG_SIZE)

    constrained_functions = [
        get_constrained_functions(c.arg_states())[0].values()
        for c in cases
    ]

    constrained_percent = [ round(len(c.arg_states()) /
            len(c.unique_results(identity_set())), 2)
        for c in cases
    ]

    def create_row(title:str,arr:list,ylabel:str):
        fig.suptitle(title,
            fontweight='bold',
            horizontalalignment='center',
            fontsize=OPTIONS.TITLE_SIZE
        )
        axes = fig.subplots(nrows=1, ncols=3,
            gridspec_kw = { 'top': 0.4 } # height
        )
        axes[0].set_ylabel(ylabel, fontsize=OPTIONS.AXES_SIZE)

        for i, ax in enumerate(axes):
            parts = ax.violinplot(
                arr[i],
                showmeans=True, showextrema=True
            )
            violin_styling(parts)

            ax.set_xlabel(f"{cases[i].name}\n\n(Harnesses with at least one "\
                    f"assumption: {constrained_percent[i]})",
                fontweight='normal',
                fontsize=OPTIONS.AXES_SIZE,
                horizontalalignment='center',
            )

    create_row("",#"Constrained parameters per constrained function",
        constrained_functions,
        "Percentage or constrained parameters [%]"
    )

    return fig
