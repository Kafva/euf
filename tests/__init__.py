import sys
from itertools import zip_longest
sys.path.append('../')

from src import BASE_DIR

zip_longest
TEST_DIR =  f"{BASE_DIR}/tests"
RESULT_DIR = f"{BASE_DIR}/results"

def check_cbmc_csv(path1:str, path2:str):
    with open(path1, mode='r', encoding='utf8' ) as f1:
        with open(path2, mode ='r', encoding='utf8') as f2:
            for line1,line2 in zip_longest(f1.readlines(), f2.readlines()):
                # The runtime field may differ
                split1 = line1.split(";")
                del split1[3]
                split2 = line2.split(";")
                del split2[3]
                assert ''.join(split1) == ''.join(split2)


