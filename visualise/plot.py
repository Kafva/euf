import os
from textwrap import wrap
from itertools import compress

import matplotlib.pyplot as plt
from matplotlib.figure import Figure
from scipy.stats import mannwhitneyu
from numpy.random import normal
from sklearn.metrics._plot.confusion_matrix import \
        ConfusionMatrixDisplay, confusion_matrix
from statsmodels.stats.contingency_tables import mcnemar

from src.types import AnalysisResult, HarnessType
from src.util import flatten, print_err, print_info
from visualise.case import Case
from visualise.util import get_constrained_functions, \
        get_reductions_per_trial, identity_set
from visualise import OPTIONS, ROUNDING

def violin_styling(parts):
    for pc in parts['bodies']:
        pc.set_facecolor(OPTIONS.PINK)
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

    def create_row(title:str,ylabel:str,index:int,unique_only:bool):
        subfig.suptitle(title,fontweight='bold',
                horizontalalignment='center',
                fontsize=OPTIONS.TITLE_SIZE
        )
        axes = subfig.subplots(nrows=1, ncols=1)
        axes.set_ylabel(ylabel, fontsize=OPTIONS.AXES_SIZE)

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

        # Wrap the bar name text to X chars
        bar_names = [ '\n'.join(wrap(l, OPTIONS.PLOT_WRAP_CHARS))
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

            axes.bar(bar_names, cases_dists[i],
                    width = OPTIONS.PLOT_WIDTH,
                    label = case.name,
                    color = [ cases[i].color ],
                    bottom = bottom,
                    edgecolor='white'
            )

        if index==0:
            axes.legend(loc='upper left')


    if len(harness_types & {HarnessType.NONE}) == 1:
        title = "Invalid preconditions observed amongst changed functions"
        ylabel="Changed functions [%]"
    elif len(harness_types & identity_set()) >= 1:
        title = "Distribution of CBMC results during identity verification"
        ylabel="Functions with valid preconditions [%]"
    else:
        title = "Distribution of CBMC results during standard verification"
        ylabel="Functions which passed identity "\
                "verification [%]"

    #create_row(title + " (with duplicates)",ylabel,0,unique_only=False)
    #create_row("Without duplicates",ylabel,1,unique_only=True)
    create_row(title+" (without duplicates)",ylabel,0,unique_only=True)

    return fig


def correctness_p_value(filepath: str):
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

    TODO: This is not well suited for comparing against the base-classification.
    '''
    if not os.path.isfile(filepath):
        print_err(f"Not found {filepath}")
        return

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
    ConfusionMatrixDisplay(cnf_matrix,
        display_labels=["equivalent","influential"]
    ).plot()

    res = mcnemar(cnf_matrix)
    print_info(f"P-value: {res.pvalue}") # type: ignore

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

def reduction_p_value(cases: list[Case]):
    '''
    == Mann-Whitney test (non-parametric) ==
    The reference value that we compare against
    is an array of reductions normally distributed around
    REDUCTION_REF_MEAN. This value is completely arbitrary
    but shows us if the reductions follow a normal distribution around R
    If we include all cases without any reductions, this analysis never
    yields any significance, the complete result is thus not normally
    distributed around any value above 0. If we exclude these cases
    we can almost derive some patterns:
    The pattern becomes clearer if we exclude expat since this case
    only had one reduction case.
    
    H_{0}: The reductions follow a normal distribution
    around or below REDUCTION_REF_MEAN
    
    H_{1}: The reductions follow a normal distribution
    above or equal to REDUCTION_REF_MEAN
    '''
    if OPTIONS.P_VALUES:
        change_set_reductions = [ get_reductions_per_trial("Change set",
            c.base_change_set, c.reduced_change_set, percent=True
            ) for c in [ cases[0], cases[2]] ]

        flat_reductions = flatten(change_set_reductions)
        flat_reductions = [ r for r in flat_reductions if r!=0 ]

        # 'greater': the distribution underlying x is stochastically greater
        # than the distribution underlying y, i.e. F(u) < G(u) for all u.
        ref_dist = normal(loc=OPTIONS.REDUCTION_REF_MEAN,
            scale=OPTIONS.REDUCTION_REF_MEAN/100,
            size=len(flat_reductions),
        )
        ref_values = list(map(abs, ref_dist))

        stat_result = mannwhitneyu(
            flat_reductions, ref_values, alternative='greater', method='auto'
        )
        print("!> Reduction statistic: ", stat_result)

def plot_reductions(cases: list[Case],percent:bool=True) -> Figure:
    '''
    We want to show the average reduction, stdev from the average and the
    extreme values, a violin plot is somewhat suitable for this
    '''
    change_set_reductions = [ get_reductions_per_trial("Change set",
        c.base_change_set, c.reduced_change_set, percent=percent
    ) for c in cases ]

    trans_set_reductions = [ get_reductions_per_trial("Transitive set",
        c.trans_set_without_reduction, c.trans_change_set, percent=percent
    ) for c in cases ]

    impact_set_reductions = [ get_reductions_per_trial("Impact set",
        c.impact_set_without_reduction, c.impact_set, percent=percent
    ) for c in cases ]


    fig = plt.figure(figsize=OPTIONS.FIG_SIZE)
    subfigs = fig.subfigures(nrows=3, ncols=1)

    def create_row(title:str,index:int,arr:list,label:str):
        subfigs[index].suptitle(title,
            fontweight='bold',
            horizontalalignment='center',
            fontsize=OPTIONS.MULTI_ROW_TITLE_SIZE
        )
        axes = subfigs[index].subplots(nrows=1, ncols=3)
        unit = '%' if percent else '#'
        axes[0].set_ylabel(f"Items removed from {label} set [{unit}]",
            fontsize=OPTIONS.AXES_SIZE,
        )

        for i, ax in enumerate(axes):
            parts = ax.violinplot(
                arr[i],
                showmeans=True, showextrema=True
            )
            violin_styling(parts)
            if index==2:
                ax.set_xlabel(cases[i].name,
                    fontweight='normal',
                    fontsize=OPTIONS.AXES_SIZE,
                    horizontalalignment='center',
                )

            if percent and len(OPTIONS.VIOLIN_YLIM)!=0:
                ax.set_ylim(OPTIONS.VIOLIN_YLIM)

    create_row("Base change set reduction", 0, change_set_reductions,
        "change"
    )
    create_row("Transitive change set reduction", 1, trans_set_reductions,
        "transitive"
    )
    create_row("Impact set reduction", 2, impact_set_reductions,
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
        axes = fig.subplots(nrows=1, ncols=3)
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

    create_row("Constrained parameters per constrained function",
        constrained_functions,
        "Percentage or constrained parameters [%]"
    )

    return fig
