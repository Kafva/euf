-- The symbol enumeration will provide some names which have a macro prefix (big2_ or little2_)
-- any rename instances which start with these prefixes should be handled
-- using '*' on the 'PREFIX(basename)' string rather than with ccls

-- This means that we lose cross TU replacement (unless we use cfdo or something)
-- We will only pass symbols that need a '*' rename to this function


function Prefix_replace(arg)
end


local function euf_dir()
	local str = debug.getinfo(2, "S").source:sub(2)
	return str:match("(.*/).*/")
end


-- Add the local lspconfig repo to the runtime path
vim.api.nvim_command("let &runtimepath.='," .. euf_dir() .. "nvim-lspconfig'")

-- Setup the lsp and connect ccls
require('lspconfig').ccls.setup{ filetypes = { "c" }  }


