-- Add the local lspconfig repo to the runtime path
vim.api.nvim_command("let &runtimepath.=',/home/jonas/Repos/euf/nvim-lspconfig'")

-- Setup the lsp and connect ccls
require('lspconfig').ccls.setup{ filetypes = { "c" }  }


SUFFIX = "_old_b026324c6904b2a"

-- Define the rename function
-- cd ~/.cache/euf/oniguruma-65a9b1aa && /usr/bin/nvim -n --clean -u ~/Repos/euf/scripts/init.lua -c ":call feedkeys(':lua Rename{filepath = \"/home/jonas/.cache/euf/oniguruma-65a9b1aa/st.c\", name = \"rehash\", line = 314, column = 1 }')" -E -s <(echo iiiiiiiiiiiiiiiiiiiiiiiiiii) regexec.c; cd -



local function dump(obj)
	return obj.filepath .. " " .. obj.name .. " " .. obj.line .. ":" .. obj.column
end

function Rename(data)
	-- Open the given file in vim
	vim.api.nvim_command(
	"edit " .. data.filepath
	)

	-- Move to the location of the identifier
	vim.api.nvim_command(
	"call cursor(" .. data.line .. "," .. data.column .. ")"
	)
	-- Invoke a rename operation through ccls
	-- ./runtime/lua/vim/lsp/buf.lua:262
	vim.lsp.buf.rename(data.name .. SUFFIX, true, true)
	print("Done: " .. dump(data) )

	vim.api.nvim_feedkeys("<cr>", "n", false)
	vim.api.nvim_feedkeys("<cr>", "n", false)
	vim.api.nvim_feedkeys("<cr>", "n", false)
	vim.api.nvim_feedkeys("ZZ", "n", false)

	--vim.cmd("wa! " ..  data.filepath .. "r")
	--vim.cmd("echon 'AAAAAAAAAA'")
end

