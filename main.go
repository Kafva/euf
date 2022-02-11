package main

import (
	"os"
	flag "github.com/spf13/pflag"
	. "github.com/Kafva/euf/lib"	
)

func main() {
	// The desired interface:
	// 	./euf --dep ../oniguruma --commit-current <...> --commit-new <...> ../jq

	HELP 		:= flag.BoolP("help", "h", false, "Show this help message and exit")
	DEBUG 		 =  flag.BoolP("Debug", "D", false, "Print debug information")
	DEPENDENCY_DIR 	:= flag.StringP("dependency", "d", "", "Path to the directory with source code for the dependency to upgrade")
	CURRENT_COMMIT 	:= flag.StringP("commit-current", "c", "", "Git hash of the current commit in the dependency used by the project")
	NEW_COMMIT 	:= flag.StringP("commit-new", "n", "", "Git hash of the updated commit in the dependency used by the project")
	
	flag.Usage = DetailUsage
	flag.Parse()
	
	if *HELP || len(os.Args) <= 1 || *DEPENDENCY_DIR == "" || *CURRENT_COMMIT == "" || *NEW_COMMIT == "" {
		DetailUsage()
		os.Exit(1)
	} 

}


