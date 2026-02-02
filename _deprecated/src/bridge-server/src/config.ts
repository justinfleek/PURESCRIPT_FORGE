/**
 * Bridge Server Configuration
 * Production-grade configuration with validation
 */
import { z } from 'zod';
import { readFileSync } from 'fs';
import { join } from 'path';
import { homedir } from 'os';

const ConfigSchema = z.object({
  port: z.number().int().positive().default(8765),
  host: z.string().default('127.0.0.1'),
  staticDir: z.string().default('./dist'),
  
  venice: z.object({
    apiKeyFile: z.string().optional(),
    apiKey: z.string().optional(),
  }).refine(
    (data) => data.apiKeyFile !== undefined || data.apiKey !== undefined,
    { message: 'Either apiKeyFile or apiKey must be provided' }
  ),
  
  lean: z.object({
    enabled: z.boolean().default(true),
    command: z.string().default('lean-lsp-mcp'),
    args: z.array(z.string()).default(['--transport', 'stdio']),
  }),
  
  storage: z.object({
    path: z.string().default(join(homedir(), '.opencode-sidepanel', 'bridge.db')),
    encryptionKey: z.string().optional(),
  }),
  
  logging: z.object({
    level: z.enum(['debug', 'info', 'warn', 'error']).default('info'),
    format: z.enum(['json', 'pretty']).default('json'),
  }),
  
  opencode: z.object({
    apiUrl: z.string().default('http://opencode.internal'),
    directory: z.string().default(process.cwd()),
    sdkPath: z.string().optional(),
    pluginPath: z.string().optional(),
  }),
});

export type Config = z.infer<typeof ConfigSchema>;

/**
 * Load configuration from environment variables and config file
 * Priority: env vars > config file > defaults
 */
export function loadConfig(): Config {
  const raw: Partial<Config> = {
    port: parseInt(process.env.SIDEPANEL_PORT ?? '8765', 10),
    host: process.env.SIDEPANEL_HOST ?? '127.0.0.1',
    staticDir: process.env.SIDEPANEL_STATIC_DIR ?? './dist',
    
    venice: {
      apiKeyFile: process.env.VENICE_API_KEY_FILE,
      apiKey: process.env.VENICE_API_KEY,
    },
    
    lean: {
      enabled: process.env.LEAN_ENABLED !== 'false',
      command: process.env.LEAN_COMMAND ?? 'lean-lsp-mcp',
      args: process.env.LEAN_ARGS?.split(' ') ?? ['--transport', 'stdio'],
    },
    
    storage: {
      path: process.env.STORAGE_PATH ?? join(homedir(), '.opencode-sidepanel', 'bridge.db'),
      encryptionKey: process.env.STORAGE_ENCRYPTION_KEY,
    },
    
    logging: {
      level: (process.env.LOG_LEVEL as Config['logging']['level']) ?? 'info',
      format: (process.env.LOG_FORMAT as Config['logging']['format']) ?? 'json',
    },
    
    opencode: {
      apiUrl: process.env.OPENCODE_API_URL ?? 'http://opencode.internal',
      directory: process.env.OPENCODE_DIRECTORY ?? process.cwd(),
      sdkPath: process.env.OPENCODE_SDK_PATH,
      pluginPath: process.env.OPENCODE_PLUGIN_PATH,
    },
  };
  
  // Try to load config file
  try {
    const configPath = process.env.CONFIG_PATH ?? join(homedir(), '.opencode-sidepanel', 'config.json');
    const configFile = JSON.parse(readFileSync(configPath, 'utf-8'));
    // Merge config file into raw (lower priority than env vars)
    Object.assign(raw, configFile);
  } catch {
    // Config file doesn't exist or is invalid, use defaults
  }
  
  return ConfigSchema.parse(raw);
}
