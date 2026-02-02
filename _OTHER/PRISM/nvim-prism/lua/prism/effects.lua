-- Prism Effects
-- Terminal-safe visual effects for Neovim

local M = {}

-- Cursor line glow effect using winblend
function M.setup_cursor_glow(preset)
  if not preset.effects or not preset.effects.glow_color then
    return
  end
  
  -- Create an autocmd to subtly highlight the cursor line
  local glow_group = vim.api.nvim_create_augroup("PrismCursorGlow", { clear = true })
  
  -- Update cursor line highlight with blend
  vim.api.nvim_create_autocmd({ "CursorMoved", "CursorMovedI" }, {
    group = glow_group,
    callback = function()
      -- Subtle blend effect on cursor line
      vim.api.nvim_set_hl(0, "CursorLine", {
        bg = preset.palette.base01,
        blend = math.floor((preset.effects.glow_intensity or 0.08) * 100),
      })
    end,
  })
end

-- Statusline accent with hero color
function M.setup_statusline_accent(preset)
  if not preset.effects then return end
  
  -- Add accent line to statusline
  local hero = preset.palette.base0A
  vim.api.nvim_set_hl(0, "StatusLineAccent", {
    fg = hero,
    bg = preset.palette.base01,
    bold = true,
  })
end

-- Subtle "breathing" animation on idle (uses timer)
function M.setup_idle_breath(preset)
  if not preset.effects then return end
  
  local breathing = false
  local breath_timer = nil
  local base_bg = preset.palette.base00
  
  -- This is a very subtle effect - only changes blend slightly
  local function breathe()
    if not breathing then
      if breath_timer then
        breath_timer:stop()
        breath_timer:close()
        breath_timer = nil
      end
      return
    end
    
    -- Subtle breathing cycle (4 second period)
    local t = (vim.loop.now() % 4000) / 4000
    local intensity = math.sin(t * math.pi * 2) * 0.02 + 0.98
    
    -- Only affects winblend of floating windows
    for _, win in ipairs(vim.api.nvim_list_wins()) do
      local cfg = vim.api.nvim_win_get_config(win)
      if cfg.relative ~= "" then
        pcall(vim.api.nvim_win_set_option, win, "winblend", math.floor((1 - intensity) * 15))
      end
    end
  end
  
  -- Start breathing after 30s idle
  local idle_timer = vim.loop.new_timer()
  idle_timer:start(30000, 0, vim.schedule_wrap(function()
    breathing = true
    breath_timer = vim.loop.new_timer()
    breath_timer:start(0, 100, vim.schedule_wrap(breathe))
  end))
  
  -- Stop on any activity
  local activity_group = vim.api.nvim_create_augroup("PrismBreath", { clear = true })
  vim.api.nvim_create_autocmd({ "CursorMoved", "CursorMovedI", "TextChanged", "TextChangedI" }, {
    group = activity_group,
    callback = function()
      breathing = false
      idle_timer:stop()
      idle_timer:start(30000, 0, vim.schedule_wrap(function()
        breathing = true
      end))
    end,
  })
end

-- Flash effect on save (milestone celebration)
function M.setup_save_flash(preset)
  local flash_group = vim.api.nvim_create_augroup("PrismSaveFlash", { clear = true })
  
  vim.api.nvim_create_autocmd("BufWritePost", {
    group = flash_group,
    callback = function()
      local hero = preset.palette.base0A
      
      -- Brief flash on cursor line
      vim.api.nvim_set_hl(0, "CursorLine", { bg = hero, blend = 30 })
      
      vim.defer_fn(function()
        vim.api.nvim_set_hl(0, "CursorLine", { bg = preset.palette.base01 })
      end, 150)
    end,
  })
end

return M
