from posixpath import expanduser
import sys

# '.' is needed to run from the visualise directory 
sys.path.extend(['..','.'])

OPTIONS = {
    'PLOT_WIDTH': 0.6,
    'PLOT_FONT_SIZE': 10,
    'PLOT_WRAP_CHARS': 8,
    'WRITE_MD': True,
    'PLOT': True,
    'LIST_ANALYZED': True,
    'UNIQUE_RESULTS': False,
    'RESULT_DIR': ".results/7",
    'IMPACT_DIR': ".results/7_impact",
    'ONLY_MULTI': True,
    'SAVE_FIGS': False,
    'FIGURE_DIR': f"{expanduser('~')}/Documents/XeT/x/thesis/assets/results",
    'FIG_SIZE': (19,11),
    'NO_VCC_RESULT_DIR': ".results/7_novccs",
    'RED': '#d44848',
    'BLUE': '#467fdb'
}

