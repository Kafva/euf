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

    # Proves the claim by showing that the negation
    # is unsatisfiable
    prove(lhs == rhs)

def new():
    s = Solver()

    # (a && b) == (a || c)
    # There are models that satisfy this, but if we try to
    # verify equivalance, prove(), we get a failure
    lhs = And(  Bool('a'),  Bool('b') ) 
    rhs = Or(  Bool('a'),  Bool('b') ) 

    s.add(lhs,rhs) 
    print( s.check(), s.model() )
    prove(lhs == rhs)

new()
# => sat [b = True, a = True]
# => counterexample
# => [b = True, a = False]

