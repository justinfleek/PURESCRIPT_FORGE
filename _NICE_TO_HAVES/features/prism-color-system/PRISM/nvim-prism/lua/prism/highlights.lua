-- Prism Highlights
-- Applies theme colors to Neovim highlight groups

local M = {}

-- Blend two hex colors
local function blend(fg, bg, alpha)
  if not fg or not bg then return fg or bg or "#000000" end
  
  local function hex_to_rgb(hex)
    hex = hex:gsub("#", "")
    return tonumber(hex:sub(1, 2), 16), tonumber(hex:sub(3, 4), 16), tonumber(hex:sub(5, 6), 16)
  end
  
  local fg_r, fg_g, fg_b = hex_to_rgb(fg)
  local bg_r, bg_g, bg_b = hex_to_rgb(bg)
  
  local r = math.floor(fg_r * alpha + bg_r * (1 - alpha))
  local g = math.floor(fg_g * alpha + bg_g * (1 - alpha))
  local b = math.floor(fg_b * alpha + bg_b * (1 - alpha))
  
  return string.format("#%02x%02x%02x", r, g, b)
end

function M.apply(preset, config)
  local p = preset.palette
  local s = preset.syntax
  local u = preset.ui
  local transparent = config.transparent
  local styles = config.styles or {}
  local int = config.integrations or {}
  
  local hi = function(group, opts)
    vim.api.nvim_set_hl(0, group, opts)
  end

  -- ═══════════════════════════════════════════════════════════════
  -- Editor
  -- ═══════════════════════════════════════════════════════════════
  
  hi("Normal", { fg = p.base05, bg = transparent and "NONE" or p.base00 })
  hi("NormalFloat", { fg = p.base05, bg = p.base01 })
  hi("NormalNC", { fg = p.base05, bg = transparent and "NONE" or p.base00 })
  hi("Cursor", { fg = p.base00, bg = p.base0A })
  hi("CursorLine", { bg = blend(p.base05, p.base00, 0.05) })
  hi("CursorColumn", { link = "CursorLine" })
  hi("ColorColumn", { bg = blend(p.base05, p.base00, 0.03) })
  hi("LineNr", { fg = p.base03 })
  hi("CursorLineNr", { fg = p.base05, bold = true })
  hi("SignColumn", { fg = p.base03, bg = transparent and "NONE" or p.base00 })
  hi("VertSplit", { fg = p.base02 })
  hi("WinSeparator", { fg = p.base02 })
  hi("Folded", { fg = p.base03, bg = p.base01 })
  hi("FoldColumn", { fg = p.base03 })
  hi("NonText", { fg = p.base03 })
  hi("SpecialKey", { fg = p.base03 })
  hi("Whitespace", { fg = blend(p.base03, p.base00, 0.5) })
  hi("MatchParen", { fg = p.base0A, bold = true })
  
  -- Search
  hi("Visual", { bg = blend(p.base0A, p.base00, 0.3) })
  hi("VisualNOS", { link = "Visual" })
  hi("Search", { fg = p.base00, bg = p.base0A })
  hi("IncSearch", { fg = p.base00, bg = p.base09 })
  hi("CurSearch", { link = "IncSearch" })
  hi("Substitute", { fg = p.base00, bg = p.base08 })
  
  -- Popup Menu
  hi("Pmenu", { fg = p.base05, bg = p.base01 })
  hi("PmenuSel", { fg = p.base05, bg = blend(p.base0A, p.base00, 0.2) })
  hi("PmenuSbar", { bg = p.base02 })
  hi("PmenuThumb", { bg = p.base04 })
  
  -- Messages
  hi("ErrorMsg", { fg = p.base08 })
  hi("WarningMsg", { fg = p.base09 })
  hi("ModeMsg", { fg = p.base05, bold = true })
  hi("MoreMsg", { fg = p.base0D })
  hi("Question", { fg = p.base0D })
  
  -- Tabs & Status
  hi("TabLine", { fg = p.base04, bg = p.base01 })
  hi("TabLineFill", { bg = p.base00 })
  hi("TabLineSel", { fg = p.base05, bg = p.base00, bold = true })
  hi("StatusLine", { fg = p.base05, bg = p.base01 })
  hi("StatusLineNC", { fg = p.base04, bg = p.base01 })
  
  -- Diff
  hi("DiffAdd", { bg = blend(p.base0B, p.base00, 0.15) })
  hi("DiffChange", { bg = blend(p.base09, p.base00, 0.15) })
  hi("DiffDelete", { fg = p.base08, bg = blend(p.base08, p.base00, 0.15) })
  hi("DiffText", { bg = blend(p.base09, p.base00, 0.3) })
  
  -- Spelling
  hi("SpellBad", { undercurl = true, sp = p.base08 })
  hi("SpellCap", { undercurl = true, sp = p.base09 })
  hi("SpellLocal", { undercurl = true, sp = p.base0D })
  hi("SpellRare", { undercurl = true, sp = p.base0E })

  -- ═══════════════════════════════════════════════════════════════
  -- Syntax
  -- ═══════════════════════════════════════════════════════════════
  
  hi("Comment", vim.tbl_extend("force", { fg = s.comment }, styles.comments or { italic = true }))
  hi("Constant", { fg = p.base09 })
  hi("String", { fg = s.string })
  hi("Character", { fg = s.string })
  hi("Number", { fg = s.number })
  hi("Boolean", { fg = s.number })
  hi("Float", { fg = s.number })
  
  hi("Identifier", vim.tbl_extend("force", { fg = s.variable }, styles.variables or {}))
  hi("Function", vim.tbl_extend("force", { fg = s.func }, styles.functions or {}))
  
  hi("Statement", { fg = s.keyword })
  hi("Conditional", { fg = s.keyword })
  hi("Repeat", { fg = s.keyword })
  hi("Label", { fg = s.keyword })
  hi("Operator", { fg = s.operator })
  hi("Keyword", vim.tbl_extend("force", { fg = s.keyword }, styles.keywords or {}))
  hi("Exception", { fg = s.keyword })
  
  hi("PreProc", { fg = s.keyword })
  hi("Include", { fg = s.keyword })
  hi("Define", { fg = s.keyword })
  hi("Macro", { fg = s.keyword })
  hi("PreCondit", { fg = s.keyword })
  
  hi("Type", { fg = s.type })
  hi("StorageClass", { fg = s.keyword })
  hi("Structure", { fg = s.type })
  hi("Typedef", { fg = s.type })
  
  hi("Special", { fg = p.base0C })
  hi("SpecialChar", { fg = p.base0C })
  hi("Tag", { fg = s.tag })
  hi("Delimiter", { fg = s.punctuation })
  hi("SpecialComment", { fg = s.comment, italic = true })
  hi("Debug", { fg = p.base09 })
  
  hi("Underlined", { underline = true })
  hi("Ignore", { fg = p.base03 })
  hi("Error", { fg = p.base08 })
  hi("Todo", { fg = p.base00, bg = p.base0A, bold = true })

  -- ═══════════════════════════════════════════════════════════════
  -- Treesitter
  -- ═══════════════════════════════════════════════════════════════
  
  if int.treesitter then
    hi("@variable", { fg = s.variable })
    hi("@variable.builtin", { fg = p.base0E })
    hi("@variable.parameter", { fg = s.variable, italic = true })
    hi("@variable.member", { fg = s.property })
    
    hi("@constant", { fg = p.base09 })
    hi("@constant.builtin", { fg = p.base09 })
    
    hi("@module", { fg = p.base05 })
    hi("@label", { fg = s.keyword })
    
    hi("@type", { fg = s.type })
    hi("@type.builtin", { fg = s.type })
    hi("@attribute", { fg = s.attribute })
    hi("@property", { fg = s.property })
    
    hi("@function", { fg = s.func })
    hi("@function.builtin", { fg = s.func })
    hi("@function.call", { fg = s.func })
    hi("@function.method", { fg = s.func })
    
    hi("@constructor", { fg = s.type })
    hi("@operator", { fg = s.operator })
    
    hi("@keyword", { fg = s.keyword })
    hi("@keyword.conditional", { fg = s.keyword })
    hi("@keyword.function", { fg = s.keyword })
    hi("@keyword.operator", { fg = s.keyword })
    hi("@keyword.return", { fg = s.keyword })
    
    hi("@punctuation.bracket", { fg = s.punctuation })
    hi("@punctuation.delimiter", { fg = s.punctuation })
    hi("@punctuation.special", { fg = p.base0C })
    
    hi("@string", { fg = s.string })
    hi("@string.escape", { fg = p.base0C })
    hi("@string.regexp", { fg = p.base0C })
    
    hi("@character", { fg = s.string })
    hi("@boolean", { fg = s.number })
    hi("@number", { fg = s.number })
    
    hi("@comment", { fg = s.comment, italic = true })
    hi("@comment.todo", { fg = p.base00, bg = p.base0A, bold = true })
    hi("@comment.error", { fg = p.base08, bold = true })
    hi("@comment.warning", { fg = p.base09, bold = true })
    hi("@comment.note", { fg = p.base0D, bold = true })
    
    hi("@markup.heading", { fg = s.keyword, bold = true })
    hi("@markup.italic", { italic = true })
    hi("@markup.strong", { bold = true })
    hi("@markup.raw", { fg = s.string })
    hi("@markup.link", { fg = p.base0D, underline = true })
    
    hi("@tag", { fg = s.tag })
    hi("@tag.attribute", { fg = s.attribute })
    hi("@tag.delimiter", { fg = s.punctuation })
  end

  -- ═══════════════════════════════════════════════════════════════
  -- LSP
  -- ═══════════════════════════════════════════════════════════════
  
  if int.native_lsp then
    hi("DiagnosticError", { fg = u.error })
    hi("DiagnosticWarn", { fg = u.warning })
    hi("DiagnosticInfo", { fg = u.info })
    hi("DiagnosticHint", { fg = u.accent })
    
    hi("DiagnosticUnderlineError", { undercurl = true, sp = u.error })
    hi("DiagnosticUnderlineWarn", { undercurl = true, sp = u.warning })
    hi("DiagnosticUnderlineInfo", { undercurl = true, sp = u.info })
    hi("DiagnosticUnderlineHint", { undercurl = true, sp = u.accent })
    
    hi("DiagnosticVirtualTextError", { fg = u.error, bg = blend(u.error, p.base00, 0.1) })
    hi("DiagnosticVirtualTextWarn", { fg = u.warning, bg = blend(u.warning, p.base00, 0.1) })
    hi("DiagnosticVirtualTextInfo", { fg = u.info, bg = blend(u.info, p.base00, 0.1) })
    hi("DiagnosticVirtualTextHint", { fg = u.accent, bg = blend(u.accent, p.base00, 0.1) })
    
    hi("LspReferenceText", { bg = blend(p.base05, p.base00, 0.1) })
    hi("LspReferenceRead", { bg = blend(p.base05, p.base00, 0.1) })
    hi("LspReferenceWrite", { bg = blend(p.base05, p.base00, 0.15) })
    hi("LspSignatureActiveParameter", { fg = u.accent, bold = true })
  end

  -- ═══════════════════════════════════════════════════════════════
  -- Plugin Integrations
  -- ═══════════════════════════════════════════════════════════════
  
  if int.gitsigns then
    hi("GitSignsAdd", { fg = u.success })
    hi("GitSignsChange", { fg = u.warning })
    hi("GitSignsDelete", { fg = u.error })
  end
  
  if int.telescope then
    hi("TelescopeNormal", { fg = p.base05, bg = p.base00 })
    hi("TelescopeBorder", { fg = p.base02, bg = p.base00 })
    hi("TelescopePromptTitle", { fg = p.base00, bg = u.accent, bold = true })
    hi("TelescopePreviewTitle", { fg = p.base00, bg = u.success, bold = true })
    hi("TelescopeResultsTitle", { fg = p.base00, bg = u.info, bold = true })
    hi("TelescopeSelection", { bg = blend(u.accent, p.base00, 0.2) })
    hi("TelescopeMatching", { fg = u.accent, bold = true })
  end
  
  if int.cmp then
    hi("CmpItemAbbrMatch", { fg = u.accent, bold = true })
    hi("CmpItemKindVariable", { fg = s.variable })
    hi("CmpItemKindFunction", { fg = s.func })
    hi("CmpItemKindKeyword", { fg = s.keyword })
    hi("CmpItemKindClass", { fg = s.type })
  end
  
  if int.indent_blankline then
    hi("IblIndent", { fg = p.base02 })
    hi("IblScope", { fg = p.base03 })
  end
  
  if int.lazy then
    hi("LazyH1", { fg = p.base00, bg = u.accent, bold = true })
    hi("LazyButton", { fg = p.base05, bg = p.base02 })
    hi("LazyButtonActive", { fg = p.base00, bg = u.accent })
  end
  
  if int.notify then
    hi("NotifyERRORBorder", { fg = u.error })
    hi("NotifyWARNBorder", { fg = u.warning })
    hi("NotifyINFOBorder", { fg = u.info })
    hi("NotifyDEBUGBorder", { fg = p.base03 })
    hi("NotifyTRACEBorder", { fg = p.base0E })
  end
end

return M
