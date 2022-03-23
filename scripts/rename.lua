#!/usr/bin/env lua
-- cd ~/.cache/euf/oniguruma-65a9b1aa && /usr/bin/nvim -n --clean -u ~/Repos/euf/scripts/init.lua -c ":call feedkeys(':luafile ~/Repos/euf/scripts/rename.lua')" regexec.c; cd -

local function dump(obj)
	return obj.filepath .. " " .. obj.name .. " " .. obj.line .. ":" .. obj.column
end

local function sleep(n)
	os.execute("sleep " .. tonumber(n))
end

local function split(arg)
	-- Split the given string into an array based on the delim
	-- If keys are provided, use them instead of integer indices
	local items = {}
	local i = 0
	for item in arg.str:gmatch("([^;]+);?") do
		if arg.keys ~= nil then
			items[arg.keys[i]] = item
		else
			items[i] = item	
		end
		i=i+1
	end
	return items
end

local SUFFIX = "_old_b026324c6904b2a"
local RENAME_CSV = '/home/jonas/Repos/euf/tests/data/oni_rename_short.csv'

local iter = 0
local table_headings = {}

for line in io.lines(RENAME_CSV) do
	if iter == 0 then
		-- First line should be a header
		table_headings = split{str = line}
	else
		local data = split{str = line, keys = table_headings}

		if data.filepath ~= nil and data.name ~= nil
		   and data.column ~= nil and data.line ~= nil then
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
			vim.api.nvim_command("let &ro = &ro")
		end
	end
	iter = iter + 1
end

