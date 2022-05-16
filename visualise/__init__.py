import sys, os
from dataclasses import dataclass, field
from posixpath import expanduser

if os.path.basename(os.getcwd()) != 'euf':
    print("!> The script should be invoked from the root of the repository")
    sys.exit(1)

sys.path.extend(['..'])


@dataclass(init=True)
class Options:
    # Output flags
    WRITE_MD: bool = False
    PLOT: bool = False
    LIST_ANALYZED: bool = False
    SAVE_FIGS: bool = False
    UNIQUE_ONLY: bool = False
    ONLY_MULTI: bool = False
    VERBOSITY: int = 0

    # Input configuration
    RESULT_DIR:str = ".results/12"
    IMPACT_DIR:str = ".results/12_impact"

    # Plotting constants
    PLOT_WIDTH: float = 0.6
    PLOT_FONT_SIZE: int = 10
    PLOT_WRAP_CHARS: int = 8
    EXPORT_LIGHT: bool = False
    FIGURE_DIR: str = f"{expanduser('~')}/Documents/XeT/x/thesis/assets/results"
    FIG_SIZE: tuple[int,int] = field(default_factory=lambda: (19,11))
    VIOLIN_YLIM: list[float] = field(default_factory=lambda: [0,.8])

    # Colors
    WHITE: str = '#ffffff'
    PINK: str = '#bb92ac'
    DARK_PINK: str = '#b888a6'
    RED: str = '#f0866e'
    GREEN: str = '#6ef093'
    BLUE: str = '#6e95f0'
    BLACK: str = '#1a1c1f'

OPTIONS = Options()
ROUNDING = 4

