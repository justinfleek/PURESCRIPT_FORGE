# 06-OPENCODE-CONFIG: Plugin and MCP Configuration

## Overview

This document details all OpenCode configuration required for the sidepanel to function. Configuration is stored in `~/.config/opencode/opencode.json` and controls plugin loading, MCP servers, and sidepanel-specific options.

---

## Configuration File Location

| Platform | Path |
|----------|------|
| macOS | `~/.config/opencode/opencode.json` |
| Linux | `~/.config/opencode/opencode.json` |
| Windows (WSL2) | `~/.config/opencode/opencode.json` |

If the file doesn't exist, create it.

---

## Complete Configuration Schema

```json
{
  "$schema": "https://opencode.ai/config.json",
  
  "plugin": [
    "opencode-sidepanel"
  ],
  
  "mcp": {
    "lean-lsp": {
      "type": "local",
      "command": "lean-lsp-mcp",
      "args": ["--transport", "stdio"],
      "env": {
        "LEAN_PATH": "/path/to/lean/lib"
      }
    },
    "venice-tools": {
      "type": "local", 
      "command": "venice-mcp",
      "args": []
    }
  },
  
  "sidepanel": {
    "port": 8765,
    "host": "127.0.0.1",
    "autoOpen": true,
    "theme": "dark",
    "alerts": {
      "diemWarningPercent": 0.20,
      "diemCriticalPercent": 0.05,
      "depletionWarningHours": 2,
      "soundEnabled": false
    },
    "features": {
      "countdown": true,
      "tokenCharts": true,
      "proofPanel": true,
      "timeline": true,
      "flameGraph": true,
      "terminalEmbed": false
    },
    "keyboard": {
      "enabled": true,
      "vimMode": true,
      "commandPalette": "ctrl+shift+p"
    },
    "storage": {
      "sessionRetentionDays": 30,
      "maxSnapshots": 100,
      "encryptAtRest": true
    }
  }
}
```

---

## Plugin Configuration

### Loading the Sidepanel Plugin

```json
{
  "plugin": ["opencode-sidepanel"]
}
```

The plugin is loaded from:
1. Global npm modules (`~/.npm-global/lib/node_modules/`)
2. Local project `node_modules/`
3. Nix store (if installed via Nix)

### Plugin Loading Order

Plugins load in array order. If you have multiple plugins, sidepanel should load early:

```json
{
  "plugin": [
    "opencode-sidepanel",
    "opencode-other-plugin"
  ]
}
```

### Disabling the Plugin

Comment out or remove from array:

```json
{
  "plugin": []
}
```

---

## MCP Server Configuration

MCP (Model Context Protocol) servers provide tool access to the AI assistant.

### lean-lsp Configuration

```json
{
  "mcp": {
    "lean-lsp": {
      "type": "local",
      "command": "lean-lsp-mcp",
      "args": ["--transport", "stdio"],
      "env": {
        "LEAN_PATH": ""
      }
    }
  }
}
```

**Fields:**

| Field | Type | Description |
|-------|------|-------------|
| `type` | `"local"` | Server runs locally |
| `command` | string | Executable name or path |
| `args` | string[] | Command line arguments |
| `env` | object | Environment variables |

**Transport options:**
- `stdio` - Communication via stdin/stdout (recommended)
- `tcp` - TCP socket connection

### Finding lean-lsp-mcp

In the Nix development shell, `lean-lsp-mcp` is automatically in PATH. Outside Nix:

```bash
# Check if available
which lean-lsp-mcp

# If not found, install via
npm install -g lean-lsp-mcp
# or
nix profile install github:weyl-ai/lean-lsp-mcp
```

### venice-tools Configuration (Optional)

If using Venice-specific MCP tools:

```json
{
  "mcp": {
    "venice-tools": {
      "type": "local",
      "command": "venice-mcp",
      "args": [],
      "env": {}
    }
  }
}
```

---

## Sidepanel Options

### Network Settings

```json
{
  "sidepanel": {
    "port": 8765,
    "host": "127.0.0.1"
  }
}
```

| Field | Default | Description |
|-------|---------|-------------|
| `port` | `8765` | HTTP/WebSocket server port |
| `host` | `"127.0.0.1"` | Bind address (localhost only for security) |

**Never** set `host` to `"0.0.0.0"` unless you understand the security implications.

### Auto-Open Browser

```json
{
  "sidepanel": {
    "autoOpen": true
  }
}
```

When `true`, browser opens automatically when OpenCode starts with `--serve`.

To disable auto-open and manually navigate:
```json
{
  "sidepanel": {
    "autoOpen": false
  }
}
```
Then manually open `http://localhost:8765`.

### Theme

```json
{
  "sidepanel": {
    "theme": "dark"
  }
}
```

Options:
- `"dark"` - Dark theme (recommended, matches terminal aesthetic)
- `"light"` - Light theme (available but not recommended)
- `"system"` - Follow system preference

---

## Alert Configuration

```json
{
  "sidepanel": {
    "alerts": {
      "diemWarningPercent": 0.20,
      "diemCriticalPercent": 0.05,
      "depletionWarningHours": 2,
      "soundEnabled": false
    }
  }
}
```

| Field | Default | Description |
|-------|---------|-------------|
| `diemWarningPercent` | `0.20` | Warning when balance < 20% of daily allocation |
| `diemCriticalPercent` | `0.05` | Critical when balance < 5% |
| `depletionWarningHours` | `2` | Warning when projected depletion < 2 hours |
| `soundEnabled` | `false` | Play sound on alerts |

### Alert Behavior

**Warning level:**
- UI turns amber/yellow
- Subtle animation on countdown
- Optional sound

**Critical level:**
- UI turns red
- Pulse animation
- Optional alert sound

---

## Feature Toggles

```json
{
  "sidepanel": {
    "features": {
      "countdown": true,
      "tokenCharts": true,
      "proofPanel": true,
      "timeline": true,
      "flameGraph": true,
      "terminalEmbed": false
    }
  }
}
```

| Feature | Default | Description |
|---------|---------|-------------|
| `countdown` | `true` | Diem reset countdown timer |
| `tokenCharts` | `true` | Usage visualization charts |
| `proofPanel` | `true` | Lean4 proof status panel |
| `timeline` | `true` | Time-travel debugging |
| `flameGraph` | `true` | Performance visualization |
| `terminalEmbed` | `false` | Embedded terminal view |

Disable features to reduce complexity or improve performance:

```json
{
  "sidepanel": {
    "features": {
      "proofPanel": false,
      "flameGraph": false
    }
  }
}
```

---

## Keyboard Configuration

```json
{
  "sidepanel": {
    "keyboard": {
      "enabled": true,
      "vimMode": true,
      "commandPalette": "ctrl+shift+p"
    }
  }
}
```

| Field | Default | Description |
|-------|---------|-------------|
| `enabled` | `true` | Enable keyboard shortcuts |
| `vimMode` | `true` | Enable Vim-style navigation |
| `commandPalette` | `"ctrl+shift+p"` | Key combo for command palette |

### Vim Mode Keys (when enabled)

| Key | Action |
|-----|--------|
| `j` / `k` | Navigate down / up |
| `gg` | Go to top |
| `G` | Go to bottom |
| `/` | Search |
| `n` / `N` | Next / previous search result |
| `Esc` | Close palette / cancel |

---

## Storage Configuration

```json
{
  "sidepanel": {
    "storage": {
      "sessionRetentionDays": 30,
      "maxSnapshots": 100,
      "encryptAtRest": true
    }
  }
}
```

| Field | Default | Description |
|-------|---------|-------------|
| `sessionRetentionDays` | `30` | Auto-delete sessions older than N days |
| `maxSnapshots` | `100` | Maximum state snapshots to keep |
| `encryptAtRest` | `true` | Encrypt session data at rest |

### Storage Location

Session data stored in:
- macOS: `~/Library/Application Support/opencode-sidepanel/`
- Linux: `~/.local/share/opencode-sidepanel/`

---

## Environment Variables

In addition to config file, some options can be set via environment variables:

| Variable | Description | Config Override |
|----------|-------------|-----------------|
| `SIDEPANEL_PORT` | Server port | `sidepanel.port` |
| `SIDEPANEL_DEBUG` | Enable debug logging | N/A |
| `VENICE_API_KEY_FILE` | Path to API key file | N/A |

Environment variables override config file values.

---

## Minimal Configuration

The smallest working configuration:

```json
{
  "plugin": ["opencode-sidepanel"]
}
```

All other options use defaults.

---

## Development Configuration

For development, enable more verbose options:

```json
{
  "$schema": "https://opencode.ai/config.json",
  "plugin": ["opencode-sidepanel"],
  "sidepanel": {
    "port": 8765,
    "autoOpen": true,
    "features": {
      "countdown": true,
      "tokenCharts": true,
      "proofPanel": true,
      "timeline": true,
      "flameGraph": true,
      "terminalEmbed": true
    }
  }
}
```

Set environment variable for debug logging:

```bash
export SIDEPANEL_DEBUG=1
opencode --serve
```

---

## Production Configuration

For daily use, a more conservative configuration:

```json
{
  "$schema": "https://opencode.ai/config.json",
  "plugin": ["opencode-sidepanel"],
  "mcp": {
    "lean-lsp": {
      "type": "local",
      "command": "lean-lsp-mcp",
      "args": ["--transport", "stdio"]
    }
  },
  "sidepanel": {
    "port": 8765,
    "autoOpen": true,
    "theme": "dark",
    "alerts": {
      "diemWarningPercent": 0.20,
      "diemCriticalPercent": 0.05,
      "soundEnabled": false
    },
    "features": {
      "countdown": true,
      "tokenCharts": true,
      "proofPanel": false,
      "timeline": false,
      "flameGraph": false,
      "terminalEmbed": false
    },
    "storage": {
      "sessionRetentionDays": 14,
      "encryptAtRest": true
    }
  }
}
```

---

## Validating Configuration

```bash
# Validate config syntax
opencode config validate

# Show effective config (with defaults)
opencode config show

# Test plugin loads
opencode --dry-run
```

---

## Troubleshooting

### "Plugin not found: opencode-sidepanel"

Plugin not installed or not in path:

```bash
# Install globally
npm install -g opencode-sidepanel

# Or verify nix shell active
nix develop
```

### "MCP server failed to start"

Check command is available:

```bash
which lean-lsp-mcp

# If not found, verify nix shell or install
```

### Config changes not taking effect

OpenCode caches config on startup:

```bash
# Restart OpenCode
opencode --serve  # Stop with Ctrl+C first
```

### Invalid JSON syntax

Validate JSON:

```bash
cat ~/.config/opencode/opencode.json | jq .
```

---

## Related Specifications

- `05-DEVELOPMENT-SETUP.md` - Initial environment setup
- `21-PLUGIN-SYSTEM.md` - Plugin event hooks
- `27-MCP-CONFIGURATION.md` - MCP server details
- `28-TUI-COMMUNICATION.md` - TUI integration

---

*"Configuration should be obvious. If you need documentation, the defaults are wrong."*
