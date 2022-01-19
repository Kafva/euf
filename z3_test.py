#!/usr/bin/env python3
# pip3 install --user z3-solver
from z3 import *

def basic():
    s = Solver()

    x = Int('x')
    y = Int('y')

    s.add(x > 2, y < 10, x + 2*y == 7)
    print( s.check(), s.model() )

    s.reset()

    # (a && b || c)    == 	(!a || c)
    lhs = Or(  And(Bool('a'),  Bool('b'), Bool('c'))  ) 
    rhs = Or(Not(Bool('a')), Bool('c'))
    s.add(lhs,rhs) 
    print( s.check(), s.model() )
    prove(lhs == rhs)



def new():
    pass

if __name__ == '__main__':
    new()
