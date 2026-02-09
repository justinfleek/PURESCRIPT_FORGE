-- Prism Color Themes for Neovim
-- 40 formally verified themes with OKLCH color science
--
-- Usage:
--   require('prism').setup({ preset = 'fleek' })
--   vim.cmd('colorscheme prism')
--   :Prism <preset_name>

local M = {}

M.config = {
  preset = "fleek",
  transparent = false,
  terminal_colors = true,
  styles = {
    comments = { italic = true },
    keywords = {},
    functions = {},
    variables = {},
  },
  integrations = {
    treesitter = true,
    native_lsp = true,
    telescope = true,
    cmp = true,
    gitsigns = true,
    indent_blankline = true,
    mini = true,
    nvim_tree = true,
    neo_tree = true,
    which_key = true,
    lazy = true,
    notify = true,
  },
}

-- Load presets
M.presets = require("prism.presets")

-- Get list of available themes
function M.list()
  local names = {}
  for name, _ in pairs(M.presets) do
    table.insert(names, name)
  end
  table.sort(names)
  return names
end

-- Apply a theme
function M.load(preset_name)
  preset_name = preset_name or M.config.preset
  local preset = M.presets[preset_name]
  
  if not preset then
    vim.notify("Prism: Unknown preset '" .. preset_name .. "'", vim.log.levels.ERROR)
    vim.notify("Available: " .. table.concat(M.list(), ", "), vim.log.levels.INFO)
    return
  end
  
  -- Clear existing
  if vim.g.colors_name then
    vim.cmd("hi clear")
  end
  
  vim.o.termguicolors = true
  vim.o.background = preset.mode == "light" and "light" or "dark"
  vim.g.colors_name = "prism-" .. preset_name
  
  -- Apply highlights
  require("prism.highlights").apply(preset, M.config)
  
  -- Apply terminal colors
  if M.config.terminal_colors then
    require("prism.terminal").apply(preset)
  end
end

-- Setup function
function M.setup(opts)
  M.config = vim.tbl_deep_extend("force", M.config, opts or {})
  
  -- Create commands
  vim.api.nvim_create_user_command("Prism", function(args)
    M.load(args.args ~= "" and args.args or nil)
  end, {
    nargs = "?",
    complete = function()
      return M.list()
    end,
    desc = "Apply a Prism theme",
  })
  
  vim.api.nvim_create_user_command("PrismList", function()
    local themes = M.list()
    vim.notify("Prism themes (" .. #themes .. "):\n" .. table.concat(themes, "\n"), vim.log.levels.INFO)
  end, { desc = "List all Prism themes" })
  
  -- Create colorscheme command
  vim.api.nvim_create_autocmd("ColorScheme", {
    pattern = "prism*",
    callback = function(ev)
      local name = ev.match:gsub("^prism%-?", "")
      if name ~= "" and M.presets[name] then
        M.load(name)
      elseif M.config.preset then
        M.load(M.config.preset)
      end
    end,
  })
end

return M
