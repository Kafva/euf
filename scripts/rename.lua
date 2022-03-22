#!/usr/bin/env lua
-- nvim -n --clean -u ~/Repos/euf/scripts/init.lua -S ~/Repos/euf/scripts/rename.lua

function dump(obj)
	print( obj.filepath .. " " .. obj.name .. " " .. obj.line .. ":" .. obj.column )
end

function sleep(n)
	os.execute("sleep " .. tonumber(n))
end

function split(arg)
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
		data = split{str = line, keys = table_headings}

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

			-- Wait for ccls to connect
			connected_clients = vim.inspect(vim.lsp.buf_get_clients())
			while #connected_clients == 0 do
				connected_clients = vim.inspect(vim.lsp.buf_get_clients())
				sleep(4)
			end
			dump(data)
			print(connected_clients)
			
			-- Invoke a rename operation through ccls
			vim.lsp.buf.rename(data.name .. SUFFIX)
		end
	end

	iter = iter + 1
end

