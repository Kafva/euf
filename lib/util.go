package lib

import (
	"fmt"
	"os"
	flag "github.com/spf13/pflag"
)

func Die(strs ... interface{}) {
	strs = append(strs, "\n")
	fmt.Fprint(os.Stderr, strs ...)
	os.Exit(-1)
}

func Debug(strs ... interface{}) {
	if *DEBUG {
		fmt.Println(strs ...)
	}
}

func DetailUsage(){
	fmt.Printf("Usage:\n%s <project>\n", os.Args[0])
	flag.PrintDefaults()
	if RELEASE {
		fmt.Println(HELP_STR + "\n(Release version)")
	} else {
		fmt.Println(HELP_STR + "\n(Development version)")
	}
}
