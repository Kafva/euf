package lib

import (
	"fmt"
	"os"
	"runtime/debug"

	flag "github.com/spf13/pflag"
)

func Dump(obj interface{}) {
	fmt.Printf("+%v\n", obj)
} 

func CheckError(err error){
	if err != nil {
		debug.PrintStack()
		Die(err)
	}
}

func Die(strs ... interface{}) {
	strs = append(strs, "\n")
	fmt.Printf("\033[31m=>\033[0m ")
	fmt.Fprint(os.Stderr, strs ...)
	os.Exit(-1)
}

func Debug(strs ... interface{}) {
	if *DEBUG {
		fmt.Println(strs ...)
	}
}

func Debugf(format string, args ... interface{}) {
	if *DEBUG {
		fmt.Printf(format, args ...)
	}
}

func DetailUsage(){
	fmt.Printf("Usage of %s:\n", os.Args[0])
	flag.PrintDefaults()
	if ! *DEBUG {
		fmt.Println(HELP_STR + "\n(Release version)")
	} else {
		fmt.Println(HELP_STR + "\n(Development version)")
	}
}
