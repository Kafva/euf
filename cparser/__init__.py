import sys
from pathlib import Path

# Enable importing from the root directory inside the module
sys.path.append('../')

BASE_DIR = str(Path(__file__).parent.parent.absolute())
