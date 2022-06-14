import sys, os
from dataclasses import dataclass, field
from posixpath import expanduser

if os.path.basename(os.getcwd()) != 'euf':
    print("!> The script should be invoked from the root of the repository")
    sys.exit(1)

sys.path.extend(['..'])

@dataclass(init=True)
class Options:
    WRITE_MD: bool = True
    PLOT: bool = True
    REDUCTION_IN_PERCENT: bool = True
    LIST_ANALYZED: bool = True
    SAVE_FIGS: bool = False
    UNIQUE_ONLY: bool = True
    ONLY_MULTI: bool = True
    VERBOSITY: int = 0
    DUMP_MULTI_RESULT_CSV: bool = True
    CSV_DIR: str = ".data"
    CSV_LIB_STR: str = "Library"

    # Correctness testing
    CORRECTNESS_CSV: str = ".results/trust.csv"
    P_VALUES: bool = True
    ALPHA: float = .05
    DESIRED_ACCURACY: float = .9

    # Input configuration
    RESULT_DIR:str = ".results/13"
    IMPACT_DIR:str = ".results/13_impact"

    # Plotting constants
    PLOT_WIDTH: float = 0.6
    PLOT_FONT_SIZE: int = 10
    PLOT_WRAP_CHARS: int = 8
    EXPORT_LIGHT: bool = True
    FIGURE_DIR: str = f"{expanduser('~')}/Documents/XeT/x/thesis/assets/results"
    FIG_SIZE: tuple[int,int] = field(default_factory=lambda: (19,11))
    VIOLIN_YLIM: list[float] = field(default_factory=list) #field(default_factory=lambda: [0,.8])
    DPI: int = 400

    TITLE_SIZE: int = 26
    MULTI_ROW_TITLE_SIZE: int = 18
    AXES_SIZE: int = 12
    REDUCTION_AXES_SIZE: int = 12

    # Colors
    COLORMAP: str = 'Pastel1'
    WHITE: str = '#ffffff'
    PINK: str = '#bb92ac'
    DARK_PINK: str = '#b888a6'
    RED: str = '#dd7e83'
    GREEN: str = '#83dd7e'
    BLUE: str = '#7ea4dd'
    BLACK: str = '#1a1c1f'

OPTIONS = Options()
ROUNDING = 2

