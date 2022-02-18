package main

import (
	"fmt"
	"os"
	. "github.com/Kafva/euf/lib"
	git "github.com/libgit2/git2go/v33"
	flag "github.com/spf13/pflag"
)

func main() {

	HELP 		:= flag.BoolP("help", "h", false, 
	"Show this help message and exit")
	
	DEBUG 		 =  flag.BoolP("Debug", "D", false, 
	"Print debug information")

	dependency_dir 	:= flag.StringP("dependency", "d", "", 
	"Path to the directory with source code for the dependency to upgrade")
	
	old_commit_str 	:= flag.StringP("commit-old", "o", "", 
	"Git hash of the old commit in the dependency used by the project")
	
	new_commit_str 	:= flag.StringP("commit-new", "n", "", 
	"Git hash of the updated commit in the dependency used by the project")
    
	flag.Usage = DetailUsage
	flag.Parse()
	
	if *HELP || len(os.Args) <= 1     || *dependency_dir == "" ||
		    *old_commit_str == "" || *new_commit_str == "" {
		DetailUsage()
		os.Exit(1)
	} 


	//var PROJECT = os.Args[0]

	// Approach:
	// 0. Determine what source files have been modified
	// 1. Walk the AST of the old and new version of each file
	// 2. Consider any functions with a difference in the AST composition as changed


	// Retrieve the old and new commit objects from the dependency
	repo, err := git.OpenRepository(*dependency_dir);	CheckError(err)
	
	new_commit_oid,err := git.NewOid(*new_commit_str); 	CheckError(err)
	old_commit_oid,err := git.NewOid(*old_commit_str);	CheckError(err)

	new_commit, err := repo.LookupCommit(new_commit_oid);   CheckError(err)  
	old_commit, err := repo.LookupCommit(old_commit_oid);   CheckError(err)

	new_tree,err := new_commit.Tree();			CheckError(err)	
	old_tree,err := old_commit.Tree();			CheckError(err)	

	diff_opts := git.DiffOptions{ 
		Flags: git.DiffIgnoreWhitespaceChange,
		ContextLines:   5000,
	}
	diff, err := repo.DiffTreeToTree(
		new_tree, old_tree, &diff_opts,
	); 							CheckError(err)

	delta_cnt, err := diff.NumDeltas(); 			CheckError(err)
	
	// Go through every delta (changed, deleted or added file) and sieve
	// out the modifications (M) to '.c' files
	for i := 0; i < delta_cnt; i++ {

		delta,err := diff.Delta(i); CheckError(err)	
		
		switch delta.Status {
		case git.DeltaModified:
			fmt.Printf("=> Modified: %s\n", delta.NewFile.Path)
		case git.DeltaAdded:
			fmt.Printf("=> New: %s\n", delta.NewFile.Path)
		case git.DeltaDeleted:
			fmt.Printf("=> Deleted: %s\n", delta.NewFile.Path)
		}	
	}
}
