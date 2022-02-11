package main

import (
	"os"
	"fmt"
	"bufio"
	"os/exec"
	"bytes"

	flag "github.com/spf13/pflag"
	. "github.com/Kafva/euf/lib"	
)

func main() {
	// The desired interface:
	// 	./euf --commit-current <...> --commit-new <...> --dep ../oniguruma ../jq
	//	go run ./main.go -c 69545dabdbc1f7a9fb5ebc329c0b7987052b2a44 -n 29754fab4e3e332d9d19d68d55d760be48a44c1b -d ../jq/modules/oniguruma ../jq

	HELP 		:= flag.BoolP("help", "h", false, "Show this help message and exit")
	DEBUG 		 =  flag.BoolP("Debug", "D", false, "Print debug information")
	NEW_COMMIT 	:= flag.StringP("commit-new", "n", "", "Git hash of the updated commit in the dependency")
	CURRENT_COMMIT 	:= flag.StringP("commit-current", "c", "", "Git hash of the current commit in the dependency used by the project")
	DEPENDENCY_DIR 	:= flag.StringP("dependency", "d", "", "Path to the directory with source code for the dependency to upgrade")
	
	flag.Usage = DetailUsage
	flag.Parse()
	
	if *HELP || len(flag.Args()) != 1 || *DEPENDENCY_DIR == "" || *NEW_COMMIT == "" || *CURRENT_COMMIT == "" {
		DetailUsage()
		os.Exit(1)
	} 

	PROJECT := flag.Args()[0]
	
	// Create a diff between the current and new commit at /tmp/<NEW_COMMIT>.diff
	cmd 	:= exec.Command("/home/jonas/Repos/euf/scripts/euf.sh", 
		"-c", *CURRENT_COMMIT, "-n", *NEW_COMMIT, "-d", *DEPENDENCY_DIR, PROJECT)
	var outb, errb bytes.Buffer
	cmd.Stdout = &outb
	cmd.Stderr = &errb
	err := cmd.Run()

	if err != nil {
	    Die(errb.String())
	}


	file, err := os.Open( fmt.Sprintf("/tmp/%s.diff", *NEW_COMMIT))
	if err != nil {
	    Die(err)
	}
	defer file.Close()

	scanner := bufio.NewScanner(file) // Note only supports diffs <= 64K

	// Changes outside of function body will produce FPs where the
	// body of the function before a change is still printed. 
	// To exclude these changes we will ensure that every -/+ is contained
	// inside the {...} of the function at start of each @@ context 
	for scanner.Scan() {
	    fmt.Println(scanner.Text())
	}

	if err := scanner.Err(); err != nil {
	    Die(err)
	}

}


