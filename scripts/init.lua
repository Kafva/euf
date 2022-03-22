-- Add the local lspconfig repo to the runtime path
vim.api.nvim_command("let &runtimepath.=',/home/jonas/Repos/euf/nvim-lspconfig'")

-- Setup the lsp and connect ccls
require('lspconfig').ccls.setup{ filetypes = { "c" }  }
