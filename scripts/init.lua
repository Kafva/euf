local function euf_dir()
	local str = debug.getinfo(2, "S").source:sub(2)
	return str:match("(.*/).*/")
end

-- Add the local lspconfig repo to the runtime path
vim.api.nvim_command("let &runtimepath.='," .. euf_dir() .. "nvim-lspconfig'")

-- Setup the lsp and connect ccls
require('lspconfig').ccls.setup{ filetypes = { "c" }  }
