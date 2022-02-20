package main

// #include "./go-clang-bindings/clang-c/Index.h"
// #include "./go-clang-bindings/go-clang.h"
import "C"

// Note that the comments before "C" will be converted
// to actual import statements
import (
	"os"
	"strings"

	. "github.com/Kafva/euf/lib"
	clang "github.com/go-clang/clang-v3.9/clang"
	git "github.com/libgit2/git2go/v33"
	flag "github.com/spf13/pflag"
)


func main() {
	HELP 		:= flag.BoolP("help", "h", false, 
	"Show this help message and exit")
	
	DEBUG 		 =  flag.BoolP("Debug", "D", false, 
	"Print debug information")

	dependencyDir 	:= flag.StringP("dependency", "d", "", 
	"Path to the directory with source code for the dependency to upgrade")
	
	oldCommitStr 	:= flag.StringP("commit-old", "o", "", 
	"Git hash of the old commit in the dependency used by the project")
	
	newCommitStr 	:= flag.StringP("commit-new", "n", "", 
	"Git hash of the updated commit in the dependency used by the project")
    
	flag.Usage = DetailUsage
	flag.Parse()
	
	if *HELP || len(os.Args) <= 1     || *dependencyDir == "" ||
		    *oldCommitStr == "" || *newCommitStr == "" {
		DetailUsage()
		os.Exit(1)
	} 


	//var PROJECT = os.Args[0]

	// Approach:
	// 0. Determine what source files have been modified
	// 1. Walk the AST of the old and new version of each file
	// 2. Consider any functions with a difference in the AST composition as changed


	// Retrieve the old and new commit objects from the dependency
	repo, err := git.OpenRepository(*dependencyDir);	CheckError(err)
	
	newCommitOid,err := git.NewOid(*newCommitStr); 	CheckError(err)
	oldCommitOid,err := git.NewOid(*oldCommitStr);	CheckError(err)

	newCommit, err := repo.LookupCommit(newCommitOid);   CheckError(err)  
	oldCommit, err := repo.LookupCommit(oldCommitOid);   CheckError(err)

	newTree,err := newCommit.Tree();			CheckError(err)	
	oldTree,err := oldCommit.Tree();			CheckError(err)	

	diffOpts := git.DiffOptions{ 
		Flags: git.DiffIgnoreWhitespaceChange,
		ContextLines:   5000,
	}
	diff, err := repo.DiffTreeToTree(
		newTree, oldTree, &diffOpts,
	); 							CheckError(err)

	deltaCnt, err := diff.NumDeltas(); 			CheckError(err)
	modifiedDeltas := make([]git.DiffDelta, 0, deltaCnt)
	
	// Go through every delta (changed, deleted or added file) and sieve
	// out the modifications (M) to '.c' files
	for i := 0; i < deltaCnt; i++ {
		delta,err := diff.Delta(i); CheckError(err)	

		if strings.HasSuffix(delta.NewFile.Path, ".c") && delta.Status == git.DeltaModified {
			modifiedDeltas = append(modifiedDeltas, delta)
		}
	}

	// Create a new index (a context for translation units)
	cindex := clang.NewIndex(0, 1)
	defer cindex.Dispose()

	changedFunctions := make([]Function, 0, 1000)

	// Fetch the source code for the old and new version of each modified path
	for _,d := range modifiedDeltas {

		if d.NewFile.Path != "src/euc_jp.c" {
			continue
		}
		
		Debugf("=> Modified: %s\n", d.NewFile.Path)
		newBlob, err := repo.LookupBlob(d.NewFile.Oid); CheckError(err)
		oldBlob, err := repo.LookupBlob(d.OldFile.Oid); CheckError(err)

		newContent := string(newBlob.Contents())
		oldContent := string(oldBlob.Contents())


		// Parse the content of the new and old version into 
		// TU objects with an AST that can be traversed
		tuNew := cindex.TranslationUnitFromSourceFile(d.NewFile.Path, 
			[]string{}, []clang.UnsavedFile{ 
			clang.NewUnsavedFile(d.NewFile.Path, newContent),
		})
		
		tuOld := cindex.TranslationUnitFromSourceFile(d.OldFile.Path, 
			[]string{}, []clang.UnsavedFile{ 
			clang.NewUnsavedFile(d.OldFile.Path, oldContent),
		})

		newCursor := tuNew.TranslationUnitCursor()
		oldCursor := tuOld.TranslationUnitCursor()


		//Debug("===> Old <===")
		//DumpFunctionsInTU(oldCursor)
		//Debug("===> New <===")
		//DumpFunctionsInTU(newCursor)

		FindChangedFunctions(oldCursor, newCursor, changedFunctions)
		
		for _,f := range changedFunctions {
			Debugf("\t%s\n", f.Displayname)
		}
		defer tuNew.Dispose()
		defer tuOld.Dispose()

		break
	}
}
