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

This approach assumes that the project has unit tests written in C and does not
rely on e.g. shell scripts to invoke the finished binary, jq does this....
'''
