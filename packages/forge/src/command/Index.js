// Forge.Command.Index FFI - Slash command system

import * as fs from 'fs/promises';
import * as path from 'path';

// Load custom commands from directory
export const loadCustomCommandsFFI = (commandsDir) => async () => {
  try {
    const entries = await fs.readdir(commandsDir, { withFileTypes: true });
    const commands = [];
    
    for (const entry of entries) {
      if (!entry.isDirectory() && entry.name.endsWith('.md')) {
        const filePath = path.join(commandsDir, entry.name);
        const content = await fs.readFile(filePath, 'utf-8');
        const cmd = parseCommandFile(entry.name, content);
        if (cmd) {
          commands.push(cmd);
        }
      }
    }
    
    return commands;
  } catch {
    return [];
  }
};

// Parse a command markdown file
function parseCommandFile(filename, content) {
  const name = filename.replace('.md', '');
  const lines = content.split('\n');
  
  // Extract metadata from frontmatter or first lines
  let description = '';
  let usage = `/${name}`;
  
  // Simple parsing: first non-empty line is description
  for (const line of lines) {
    const trimmed = line.trim();
    if (trimmed && !trimmed.startsWith('#')) {
      description = trimmed;
      break;
    }
  }
  
  return {
    name,
    description,
    pattern: `^/${name}\\s*(.*)?$`,
    usage,
    arguments: []
  };
}

// Execute built-in command
export const executeBuiltinFFI = (name) => (ctx) => async () => {
  try {
    switch (name) {
      case 'help':
        return {
          tag: 'Right',
          value: {
            output: formatHelpOutput(ctx.args),
            success: true,
            data: null
          }
        };
      
      case 'clear':
        return {
          tag: 'Right',
          value: {
            output: 'Session cleared.',
            success: true,
            data: JSON.stringify({ action: 'clear_session' })
          }
        };
      
      case 'compact':
        return {
          tag: 'Right',
          value: {
            output: 'History compacted.',
            success: true,
            data: JSON.stringify({ action: 'compact_history' })
          }
        };
      
      case 'config':
        return {
          tag: 'Right',
          value: {
            output: formatConfigOutput(ctx.args),
            success: true,
            data: null
          }
        };
      
      case 'status':
        return {
          tag: 'Right',
          value: {
            output: formatStatusOutput(),
            success: true,
            data: null
          }
        };
      
      default:
        return {
          tag: 'Left',
          value: `Unknown command: /${name}`
        };
    }
  } catch (err) {
    return {
      tag: 'Left',
      value: err.message
    };
  }
};

function formatHelpOutput(args) {
  if (args.length === 0) {
    return `Available commands:
  /help [command]  - Show help information
  /clear           - Clear the current session
  /compact         - Compact conversation history
  /config [key]    - Show or edit configuration
  /status          - Show system status

Type /help <command> for more info on a specific command.`;
  }
  
  const cmd = args[0];
  const helpTexts = {
    'help': 'Usage: /help [command]\n\nShows help information about available commands.',
    'clear': 'Usage: /clear\n\nClears the current session and starts fresh.',
    'compact': 'Usage: /compact\n\nCompacts the conversation history to save context space.',
    'config': 'Usage: /config [key] [value]\n\nShows or sets configuration values.',
    'status': 'Usage: /status\n\nShows current system status and diagnostics.'
  };
  
  return helpTexts[cmd] || `Unknown command: /${cmd}`;
}

function formatConfigOutput(args) {
  if (args.length === 0) {
    return 'Configuration:\n  Use /config <key> to see a specific value\n  Use /config <key> <value> to set a value';
  }
  return `Config key: ${args[0]}\nValue: (not set)`;
}

function formatStatusOutput() {
  const uptime = process.uptime();
  const memory = process.memoryUsage();
  
  return `System Status:
  Uptime: ${Math.floor(uptime)}s
  Memory: ${Math.round(memory.heapUsed / 1024 / 1024)}MB / ${Math.round(memory.heapTotal / 1024 / 1024)}MB
  Node: ${process.version}
  Platform: ${process.platform}`;
}
