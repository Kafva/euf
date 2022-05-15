from textwrap import wrap
from itertools import compress

import matplotlib.pyplot as plt
from matplotlib.figure import Figure

from src.types import AnalysisResult, HarnessType
from visualise.case import Case
from visualise.util import get_reductions_per_trial, identity_set
from visualise import OPTIONS

def plot_analysis_dists(cases: list[Case],harness_types: set[HarnessType]) \
  -> Figure:
    '''
    Not using the `unique_only` option gives the impression that expat has
    very good performance, which stems from the fact that it has analyzed
    the same few functions successfully many times.
    '''
    fig = plt.figure(figsize=OPTIONS.FIG_SIZE)
    subfigs = fig.subfigures(nrows=2, ncols=1)

    def create_row(title,ylabel,index,unique_only:bool):
        subfigs[index].suptitle(title,fontweight='bold',
                horizontalalignment='center'
        )
        axes = subfigs[index].subplots(nrows=1, ncols=1)
        axes.set_ylabel(ylabel)

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

    create_row(title + " (with duplicates)",ylabel,0,unique_only=False)
    create_row("Without duplicates",ylabel,1,unique_only=True)

    return fig

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

    def create_row(title,index,array1,label):
        subfigs[index].suptitle(title,
            fontweight='bold',
            horizontalalignment='center'
        )
        axes = subfigs[index].subplots(nrows=1, ncols=3)
        unit = '%' if percent else '#'
        axes[0].set_ylabel(f"Items removed from {label} set [{unit}]")

        for i, ax in enumerate(axes):
            parts = ax.violinplot(
                array1[i],
                showmeans=True, showextrema=True
            )
            if percent:
                ax.set_ylim(OPTIONS.VIOLIN_YLIM)

            for pc in parts['bodies']:
                pc.set_facecolor(OPTIONS.PINK)
                pc.set_edgecolor('white')
                pc.set_alpha(0.5)

            # Change colors of the mean indicators
            for partname in ('cbars','cmins','cmaxes','cmeans'):
                vp = parts[partname]
                vp.set_edgecolor(OPTIONS.DARK_PINK)
                vp.set_linewidth(2)

            if index==2:
                ax.set_xlabel(cases[i].name,
                    fontweight='normal',
                    fontsize=12,
                    horizontalalignment='center',
                )

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

#def plot_states(cases: list[Case]):
#    '''
#    Each state space analysis creates a states.json file on the form:
#    "ENTROPY_DEBUG": {
#      "parameters": [
#          {
#              "name": "label",
#              "nondet": false,
#              "states": [
#                  "arc4random_buf"
#              ]
#          },
#          {
#              "name": "entropy",
#              "nondet": true,
#              "states": []
#          }
#      ]
#    }
#
#    For the visualisation we would like to know (per case):
#        * What percentage of (analyzed/changed) functions had at least 
#        one parameter with constant state?
#
#        * Out of the functions with at least one constant parameter, how many states
#        were encountered for a parameter on average?
#
#        * Did any state space anylsis yield a harness where every parameter was
#        constrained? I.e. what percentage of parameters in a function were
#        constrained on average?
#
#    This data would highlight how useful state analysis is in regards to limiting
#    the data space of input data.
#    '''



