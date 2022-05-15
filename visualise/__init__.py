import sys
from posixpath import expanduser

# '.' is needed to run from the visualise directory 
sys.path.extend(['..','.'])

OPTIONS = {
    # Output flags
    'WRITE_MD': True,
    'PLOT': True,
    'LIST_ANALYZED': False,
    'SAVE_FIGS': False,
    'UNIQUE_RESULTS': False,
    'ONLY_MULTI': False,

    # Input configuration
    'RESULT_DIR': ".results/9",
    'IMPACT_DIR': ".results/9_impact",

    # Plotting constants
    'PLOT_WIDTH': 0.6,
    'PLOT_FONT_SIZE': 10,
    'PLOT_WRAP_CHARS': 8,
    'EXPORT_LIGHT': False,
    'FIGURE_DIR': f"{expanduser('~')}/Documents/XeT/x/thesis/assets/results",
    'FIG_SIZE': (19,11),
    'VIOLIN_YLIM': [0,.8],

    # Colors
    'WHITE': '#ffffff',
    'PINK': '#bb92ac',
    'DARK PINK': '#b888a6',
    'RED': '#f0866e',
    'GREEN': '#6ef093',
    'BLUE': '#6e95f0',
    'BLACK': '#1a1c1f'
}

