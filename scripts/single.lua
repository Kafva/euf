#!/usr/bin/env lua
-- cd ~/.cache/euf/oniguruma-65a9b1aa && /usr/bin/nvim -n --clean -u ~/Repos/euf/scripts/init.lua -c ')" regexec.c; cd -

data = {
	filepath = args[1],
	name = args[2]
	line = args[3],
	column = args[4]
}

local SUFFIX = "_old_b026324c6904b2a"
local function rename(data)
	-- Open the given file in vim
	vim.api.nvim_command(
	"edit " .. data.filepath
	)
	-- Move to the location of the identifier
	vim.api.nvim_command(
	"call cursor(" .. data.line .. "," .. data.column .. ")"
	)
	-- Invoke a rename operation through ccls
	vim.lsp.buf.rename(data.name .. SUFFIX)
	print("Done: " .. dump(data) )
end



