die(){ echo -e "$1" >&2 ; exit 1; }
finish(){
	cd $DEP_NEW 
	git checkout $ORIG_NEW_BRANCH &> /dev/null || 
		echo "Failed to switch back to $ORIG_NEW_BRANCH"

	cd $DEP_OLD
	git checkout $DEP_FILE_OLD &> /dev/null
	git checkout $ORIG_OLD_BRANCH &> /dev/null || 
		echo "Failed to switch back to $ORIG_OLD_BRANCH"
	exit $?
}

check_branch(){
	echo "$1" | grep -iqE "^[-_.A-Za-z0-9]+$"	
}

# We assume that the first argument is the CC and that the last three arguments are '-o output input'
get_cc_cmds(){
	jq "[.[] | select(.file==\"$1/$2\" or .file==\"$2\")][0].arguments[1:-3]|join(\" \")" \
		$1/compile_commands.json | xargs
}

