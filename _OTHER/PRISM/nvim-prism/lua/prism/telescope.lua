-- Prism Telescope Integration
-- Browse and preview theme presets with Telescope

local M = {}

-- Check if telescope is available
local has_telescope, telescope = pcall(require, "telescope")
if not has_telescope then
  M.preset_picker = function()
    vim.notify("Prism: Telescope not found. Use :Prism <preset_name> instead.", vim.log.levels.WARN)
  end
  return M
end

local pickers = require("telescope.pickers")
local finders = require("telescope.finders")
local conf = require("telescope.config").values
local actions = require("telescope.actions")
local action_state = require("telescope.actions.state")
local previewers = require("telescope.previewers")

local presets = require("prism.presets")

-- Category icons
local category_icons = {
  luxury = "🏛️",
  glass = "💎",
  bento = "📦",
  neumorphism = "🫧",
  responsive = "✨",
  easter_eggs = "🎮",
}

-- Generate preview content
local function generate_preview(preset)
  local lines = {
    "╭─────────────────────────────────────────╮",
    "│  " .. preset.name .. string.rep(" ", 39 - #preset.name) .. "│",
    "├─────────────────────────────────────────┤",
    "│  " .. (category_icons[preset.category] or "🎨") .. " " .. preset.category .. string.rep(" ", 34 - #preset.category) .. "│",
    "│                                         │",
    "│  " .. preset.inspiration:sub(1, 37) .. string.rep(" ", math.max(0, 37 - #preset.inspiration)) .. "│",
  }
  
  if #preset.inspiration > 37 then
    table.insert(lines, "│  " .. preset.inspiration:sub(38, 74) .. string.rep(" ", math.max(0, 37 - #preset.inspiration:sub(38, 74))) .. "│")
  end
  
  table.insert(lines, "├─────────────────────────────────────────┤")
  table.insert(lines, "│  PALETTE                                │")
  table.insert(lines, "│                                         │")
  
  -- Show key colors
  local colors = {
    { "Background", preset.palette.base00 },
    { "Surface", preset.palette.base01 },
    { "Selection", preset.palette.base02 },
    { "Comment", preset.palette.base03 },
    { "Foreground", preset.palette.base05 },
    { "Hero/Type", preset.palette.base0A },
    { "String", preset.palette.base0B },
    { "Function", preset.palette.base0D },
    { "Keyword", preset.palette.base0E },
  }
  
  for _, c in ipairs(colors) do
    local name = c[1]
    local hex = c[2]
    local padding = 12 - #name
    table.insert(lines, "│  " .. name .. ":" .. string.rep(" ", padding) .. hex .. "                │")
  end
  
  table.insert(lines, "│                                         │")
  table.insert(lines, "├─────────────────────────────────────────┤")
  table.insert(lines, "│  CODE PREVIEW                           │")
  table.insert(lines, "│                                         │")
  table.insert(lines, "│  // " .. preset.name .. "                │")
  table.insert(lines, "│  const theme = \"" .. preset.name:lower():gsub(" ", "_") .. "\";│")
  table.insert(lines, "│  type Config = { hero: Color };         │")
  table.insert(lines, "│  function apply(): void {}              │")
  table.insert(lines, "│                                         │")
  table.insert(lines, "╰─────────────────────────────────────────╯")
  
  return lines
end

-- Custom previewer that shows theme info and applies it temporarily
local theme_previewer = previewers.new_buffer_previewer({
  title = "Theme Preview",
  
  define_preview = function(self, entry, status)
    local preset = entry.value
    local lines = generate_preview(preset)
    
    vim.api.nvim_buf_set_lines(self.state.bufnr, 0, -1, false, lines)
    
    -- Apply theme temporarily for live preview
    local ok, prism = pcall(require, "prism")
    if ok then
      -- Store current theme
      if not M._original_theme then
        M._original_theme = vim.g.colors_name
      end
      -- Apply preview theme
      prism.apply(entry.preset_id)
    end
  end,
})

-- Restore original theme when closing picker
local function restore_theme()
  if M._original_theme then
    local ok, prism = pcall(require, "prism")
    if ok and M._original_theme:match("^prism%-") then
      local preset_name = M._original_theme:gsub("^prism%-", "")
      prism.apply(preset_name)
    end
    M._original_theme = nil
  end
end

-- Main picker function
function M.preset_picker(opts)
  opts = opts or {}
  
  -- Convert presets table to list
  local preset_list = {}
  for id, preset in pairs(presets) do
    table.insert(preset_list, {
      id = id,
      preset = preset,
    })
  end
  
  -- Sort by category then name
  table.sort(preset_list, function(a, b)
    if a.preset.category ~= b.preset.category then
      return a.preset.category < b.preset.category
    end
    return a.preset.name < b.preset.name
  end)
  
  pickers.new(opts, {
    prompt_title = "🎨 Prism Premium Themes",
    
    finder = finders.new_table({
      results = preset_list,
      entry_maker = function(item)
        local preset = item.preset
        local icon = category_icons[preset.category] or "🎨"
        
        return {
          value = preset,
          preset_id = item.id,
          display = icon .. " " .. preset.name,
          ordinal = preset.name .. " " .. preset.category .. " " .. (preset.inspiration or ""),
        }
      end
    }),
    
    sorter = conf.generic_sorter(opts),
    
    previewer = theme_previewer,
    
    attach_mappings = function(prompt_bufnr, map)
      -- Apply theme on selection
      actions.select_default:replace(function()
        local selection = action_state.get_selected_entry()
        actions.close(prompt_bufnr)
        
        M._original_theme = nil  -- Don't restore, we're keeping this theme
        
        local ok, prism = pcall(require, "prism")
        if ok and selection then
          prism.apply(selection.preset_id)
          vim.notify("Prism: Applied '" .. selection.value.name .. "'", vim.log.levels.INFO)
        end
      end)
      
      -- Restore on close without selection
      actions.close:enhance({
        post = function()
          restore_theme()
        end
      })
      
      return true
    end,
  }):find()
end

-- Category picker
function M.category_picker(opts)
  opts = opts or {}
  
  local categories = {
    { id = "luxury", name = "Luxury Marble", icon = "🏛️", desc = "Black marble, gold veining, obsidian" },
    { id = "glass", name = "Glassmorphism", icon = "💎", desc = "Frosted glass with blur effects" },
    { id = "bento", name = "Bento", icon = "📦", desc = "Floating card layouts" },
    { id = "neumorphism", name = "Neumorphism", icon = "🫧", desc = "Soft shadows, tactile depth" },
    { id = "responsive", name = "Responsive", icon = "✨", desc = "Themes that respond to activity" },
    { id = "easter_eggs", name = "Easter Eggs", icon = "🎮", desc = "Hidden delights and rewards" },
  }
  
  pickers.new(opts, {
    prompt_title = "🎨 Theme Categories",
    
    finder = finders.new_table({
      results = categories,
      entry_maker = function(cat)
        return {
          value = cat,
          display = cat.icon .. " " .. cat.name,
          ordinal = cat.name .. " " .. cat.desc,
        }
      end
    }),
    
    sorter = conf.generic_sorter(opts),
    
    attach_mappings = function(prompt_bufnr, map)
      actions.select_default:replace(function()
        local selection = action_state.get_selected_entry()
        actions.close(prompt_bufnr)
        
        if selection then
          -- Open preset picker filtered by category
          M.preset_picker({
            default_text = selection.value.id,
          })
        end
      end)
      
      return true
    end,
  }):find()
end

return M
