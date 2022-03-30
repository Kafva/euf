#!/usr/bin/env python3
#----------------------------#
#== http://cprover.diffblue.com/group__goto-programs.html#Binary%20Representation ==#

# Check symbol replacement status:
#		cbmc --show-symbol-table goto/xmlparse.o

import os, sys

def die(msg: str, code = 0):
    print(msg)
    exit(code)

if len(sys.argv) == 1:
    die(f"{os.path.basename(__file__)} <.gb>")


def decode_int_7bit(b_arr: bytearray):
    '''
     Interpret a stream of byte as a 7-bit encoded unsigned number.
        src/util/irep_serialisation.cpp
    '''
    res=0
    shift_distance=0

    for b in b_arr:
      res = res | (b & 0x7f)  << shift_distance
      shift_distance+=7

      if b & 0x80 == 0:
        break

    return res


def encode_int_7bit(u: int):
    '''
    Write 7 bits of `u` each time, least-significant byte first, until we have
    zero.
        src/util/irep_serialisation.cpp
    '''
    out = bytearray()

    while True:
        sub = u & 0x7f;
        u = u >> 7;
        if u==0:
            out.append(sub)
            break;
    out.append( sub | 0x80 )
    return out


content = b''

with open(sys.argv[1], mode='rb') as f:
    if (content := f.read(4)) != b'\x7fGBF': # GBF header
        die("Invalid input file")

    content += f.read(1) # Version number

    # Number of symbols in the symbol table, should be the same as:
    #   `cbmc --show-symbol-table goto/xmlrole.o | grep -c "^Symbol\."`
    symbol_cnt_bytes = f.read(2)
    symbol_count = decode_int_7bit(bytearray(symbol_cnt_bytes))
    content += symbol_cnt_bytes

    print(symbol_count)

    # Array of symbols

