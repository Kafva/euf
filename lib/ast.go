package lib

import (
	clang "github.com/go-clang/clang-v3.9/clang"
)

// Add cursors for every child of the provided cursor to the given slice
func AddChildCursors(cursor clang.Cursor, children []clang.Cursor) {
	for i  := 0; i < int(cursor.NumArguments()); i++ {
		arg := cursor.Argument(uint32(i))
		children = append(children, arg)
	}
}

// Add types for every child of the provided cursor to the given slice
func AddChildTypes(cursor clang.Cursor, children []clang.TypeKind) {
	for i  := 0; i < int(cursor.NumArguments()); i++ {
		arg := cursor.Argument(uint32(i))
		children = append(children, arg.Type().Kind())
	}
}


// Dump the names of all top-level function declarations using a cursor from a TU
func DumpFunctionsInTU(cursor clang.Cursor){
	// The Visit() method can recursively visit child nodes if necessary
	cursor.Visit( func(cursor, parent clang.Cursor) clang.ChildVisitResult {

		if cursor.IsNull() {
			return clang.ChildVisit_Continue
		}

		if cursor.Kind() == clang.Cursor_FunctionDecl && cursor.IsCursorDefinition() {
			Debugf("%s %s (\n",  cursor.ResultType().Spelling(), cursor.Spelling()  )

			// Iterate over all of the arguments to the function
			for i  := 0; i < int(cursor.NumArguments()); i++ {
				arg := cursor.Argument(uint32(i))
				Debugf("\t%s %s,\n", arg.Type().Spelling(), arg.Spelling())
			}
			Debug(")")					
		}
		return clang.ChildVisit_Continue
	})
}

// Traverse the AST of each function identified in both versions
// We consider functions with any divergence in the AST composition as 
// modified at this stage
func FindChangedFunctions(oldCursor, newCursor clang.Cursor, changedFunctions []Function){
	// - - Helper functions - - //
	GetFunctionCursors := func(cursor clang.Cursor, cursorPairs map[string]CursorPair, IsNew bool){
		cursor.Visit( func(cursor, parent clang.Cursor) clang.ChildVisitResult {

			if cursor.Kind() == clang.Cursor_FunctionDecl && cursor.IsCursorDefinition() {
				key := cursor.DisplayName()

				pair,ok := cursorPairs[key];

				if !ok {
					cursorPairs[key] = CursorPair{}
				}
				// Note that .Add() also saves the types of the function arguments
				pair.Add(cursor, IsNew)
			}
			return clang.ChildVisit_Continue
		})
	}

	cursorPairs := make(map[string]CursorPair)

	// Extract cursors for each of the top level functions in both versions
	GetFunctionCursors(oldCursor, cursorPairs, false)
	GetFunctionCursors(newCursor, cursorPairs, true)

	// To visit both pairs in parallel and compare their content we cannot
	// use the built-in recurse functionality of .Visit()
	//newCursors := make([]clang.Cursor, 0, 100)
	//oldCursors := make([]clang.Cursor, 0, 100)

	for key,pair := range cursorPairs {
		// First, check if the input arguments differ between the versions
		if len(pair.ArgsOld) != len(pair.ArgsNew) {
			changedFunctions = append(changedFunctions, makeFunction(pair))
			Debugf("=> Differ: %s\n", key)
			continue
		} else {
			// Type check the arguments
			added := false
			for i := range pair.ArgsOld {
				if pair.ArgsOld[i] != pair.ArgsNew[i] {
					added = true
					changedFunctions = append(changedFunctions, makeFunction(pair))
					break
				}
			}
			if added {
				Debugf("=> Differ: %s\n", key)
				continue
			}
		}

		// If the function prototypes have not changed, recurse down each
		// of the child nodes and continue comparing until a change is
		// encountered or the leaf nodes are reached


		Debugf("=> Same: %s\n", key)

		// Go through the children of  and add all the child nodes to an array
		//pair.New.Visit(func(cursor, parent clang.Cursor) clang.ChildVisitResult {
		//	AddChildCursors(cursor, newCursors)
		//	return clang.ChildVisit_Break
		//})
		//pair.Old.Visit(func(cursor, parent clang.Cursor) clang.ChildVisitResult {
		//	AddChildCursors(cursor, oldCursors)
		//	return clang.ChildVisit_Break
		//})

		//if len(newCursors) != len(oldCursors) {
		//	// If the number of input arguments differ
		//	AddToChanged(pair, changedFunctions)
		//	continue
		//} else {
		//	added := false

		//	// Type check the arguments, if any differ
		//	// continue to the next function
		//	for i := range newCursors {
		//		if newCursors[i].Type().Kind() != oldCursors[i].Type().Kind() {
		//			AddToChanged(pair, changedFunctions)
		//			added = true
		//			break
		//		}
		//	}

		//	if added {
		//		continue
		//	}

		//}
	}
}

