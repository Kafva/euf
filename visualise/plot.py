import matplotlib.pyplot as plt
from itertools import compress
from textwrap import wrap

from src.types import AnalysisResult
from visualise.case import Case
from visualise import OPTIONS


def plot_analysis_dists(cases: list[Case],ident:bool=False):
    '''
    Not using the `unique_results` option gives the impression that expat has
    very good performance, which stems from the fact that it has analyzed
    the same few functions successfully many times.
    '''
    fig = plt.figure(figsize=OPTIONS['FIG_SIZE'])
    subfigs = fig.subfigures(nrows=2, ncols=1)

    def create_row(title,index,unique_results:bool):
        subfigs[index].suptitle(title,fontweight='bold',
                horizontalalignment='center'
        )
        axes = subfigs[index].subplots(nrows=1, ncols=1)
        axes.set_ylabel('')

        cases_dists = [ c.analysis_dist(
                            ident=ident,
                            unique_results=unique_results
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
        bar_names = [ '\n'.join(wrap(l, OPTIONS['PLOT_WRAP_CHARS'])) for l in bar_names ]

        # Color-code a bar plot for each case
        for i,case in enumerate(cases):
            # The bottom value must be correctly set to the sum of the previous
            # bars, otherwise overlaps will occur
            match i:
                case 1: bottom = cases_dists[0]
                case 2: bottom = [ x+y for x,y in zip(cases_dists[0],cases_dists[1]) ]
                case _: bottom = 0

            axes.bar(bar_names, cases_dists[i],
                    width = OPTIONS['PLOT_WIDTH'],
                    label = case.name,
                    color = [ cases[i].color ],
                    bottom = bottom,
                    edgecolor='white'
            )

        if index==0:
            axes.legend(loc='upper left')

    title = f"Distribution of CBMC {'identity ' if ident else ''}analysis "\
            "results (with duplicates)"

    create_row(title,0,unique_results=False)
    create_row("Without duplicates",1,unique_results=True)

def plot_reductions(cases: list[Case],percent:bool=True):
    '''
    We want to show the average reduction, stdev from the average and the
    extreme values, a violin plot is somewhat suitable for this
    '''
    change_set_reductions = [ c.change_set_reductions_per_trial(percent=percent)
            for c in cases ]
    trans_set_reductions =  [ c.trans_set_reductions_per_trial(percent=percent)
            for c in cases ]
    impact_set_reductions = [ c.impact_set_reductions_per_trial(percent=percent)
            for c in cases ]

    fig = plt.figure(figsize=OPTIONS['FIG_SIZE'])
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
                ax.set_ylim(OPTIONS['VIOLIN_YLIM'])

            for pc in parts['bodies']:
                 pc.set_facecolor('#a9d1d0')
                 pc.set_edgecolor('white')
                 pc.set_alpha(0.5)

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

