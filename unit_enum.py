#!/usr/bin/env python3
'''
To compare EUF with unit test coverage we need a way of creating a structure akin to 
tests = {
  test1: {
    func1,func2
  }
  test2: {
    func2
  },
  test3: {
    func3,func4
  }
}

1. Enumerate all functions in the main project that call a dep function
   We should exclude static functions in this enumeration to avoid excessive FPs
   otherwise we will incorrectly label functions as using the dep
2. With a list of all functions in the main project that call a dep function +
   the non-static functions in the dep, traverse the AST of all test files
   to create the mapping above.

This approach assumes that the project has a considerable ammount of 
unit tests written in C that actually invoke the dependency's API.
Git and Gdb both use expat but only have 1-3 unit tests that touches it so we
would need to run tests from several projects for each update to get a decent
data set.

Maybe implement this just to see how many functions are touched by tests...


Most projects test their high-level functionality by actually executing the program in question and
supplying `input,expected output` tuples. Unlike unit tests, it is not immediatelly apparent which
tests can reach a dependency when using this approach

We could either limit ourselves to unit tests (where we know exactly which tests
reach a specific dependency change through source code reachability analsyis) or...

1. Patch the dependency so that EVERY api function call is logged

foo(){ traceback >> /tmp/log
        call_stack;
...
}

> run_test jq '.[] | keys' test 
    # Check test result
    # Check invoked log


2. We can then look at the log after a test and the test results to determine
if a test that reached a changed failed or not


There are several existing solutions for this:
    https://llvm.org/docs/XRay.html
    https://gcc.gnu.org/onlinedocs/gcc-8.1.0/gcc/Instrumentation-Options.html
    http://cmdlinelinux.blogspot.com/2020/01/i-have-been-chasing-for-toolcompiler.html



    make clean&&make CC=clang CFLAGS="-g -fxray-instrument -fxray-instruction-threshold=50" main&&./main
    llvm-xray account main

'''
