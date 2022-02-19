package main

import (
	"os"
	"strings"

	. "github.com/Kafva/euf/lib"
	clang "github.com/go-clang/clang-v3.9/clang"
	git "github.com/libgit2/git2go/v33"
	flag "github.com/spf13/pflag"
)

//clang "github.com/go-clang/clang-v3.9/clang"
//. "github.com/Kafva/euf/go-clang-bindings"

// Example of how the Go bindings can be used
// 	https://github.com/go-clang/v3.9/blob/master/cmd/go-clang-dump/main.go
func ParseSource(){


}

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

	// Fetch the source code for the old and new version of each modified path
	for _,d := range(modifiedDeltas) {
		Debugf("=> Modified: %s\n", d.NewFile.Path)
		newBlob, err := repo.LookupBlob(d.NewFile.Oid); CheckError(err)
		oldBlob, err := repo.LookupBlob(d.OldFile.Oid); CheckError(err)

		newContent := string(newBlob.Contents())
		oldContent := string(oldBlob.Contents())

		print(newContent)
		print(oldContent)
		
		// Extract the top level functions definitions in both versions
		
		// Traverse the AST of each function identified in both versions
		// We consider functions with any divergence in the AST composition as 
		// modified at this stage

		// Basic usage example
		idx := clang.NewIndex(0, 1)
		defer idx.Dispose()

		tuArgs := []string{}
		if len(flag.Args()) > 0 && flag.Args()[0] == "-" {
			tuArgs = make([]string, len(flag.Args()[1:]))
			copy(tuArgs, flag.Args()[1:])
		}

		tu := idx.ParseTranslationUnit("toy/src/main.c", tuArgs, nil, 0)
		defer tu.Dispose()

		break
	}
}
