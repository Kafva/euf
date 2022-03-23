#!/usr/bin/env nvim
" cd ~/.cache/euf/oniguruma-65a9b1aa && /usr/bin/nvim -n --clean -u ~/Repos/euf/scripts/init.lua -c ":call feedkeys(':so ~/Repos/euf/scripts/rename.vim')" regexec.c; cd -

let SUFFIX = "_old_b026324c6904b2a"

let i = 0

let files = [ "/home/jonas/.cache/euf/oniguruma-65a9b1aa/st.c", "/home/jonas/.cache/euf/oniguruma-65a9b1aa/regcomp.c"]
let names = [ "rehash", "setup_look_behind" ]
let lines = [ 314, 3121 ]
let cols = [1,1]

" Invoke single renames (for specific files) from python, that should at least work?
" But we would need like 900 manual <cr> presses....
while i <= 1
	" Open the given file in vim
	exec 'edit '. files[i]
	
	" Move to the location of the identifier
	call cursor(lines[i], cols[i])

	" Invoke a rename operation through ccls
	call feedkeys(':lua vim.lsp.buf.rename("' . names[i] . SUFFIX . '")' . "\<cr>")
	echon "Done: " . files[i]
	let &ro = &ro

	let i = i + 1
endwhile


