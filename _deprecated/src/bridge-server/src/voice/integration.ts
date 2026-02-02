/**
 * Voice Engine Integration
 * 
 * Integrates Python voice engine with Bridge Server.
 * Spawns Python FastAPI service and proxies requests.
 */

import { spawn, ChildProcess } from 'child_process';
import { join } from 'path';
import pino from 'pino';

const logger = pino({ name: 'voice-integration' });

export interface VoiceServiceConfig {
  pythonPath?: string;
  voiceEnginePath?: string;
  port?: number;
  veniceApiKey?: string;
  dbPath?: string;
}

export class VoiceService {
  private process: ChildProcess | null = null;
  private port: number;
  private baseUrl: string;

  constructor(private config: VoiceServiceConfig) {
    this.port = config.port ?? 8001;
    this.baseUrl = `http://localhost:${this.port}`;
  }

  /**
   * Start Python voice engine service
   */
  async start(): Promise<void> {
    if (this.process) {
      logger.warn('Voice service already running');
      return;
    }

    const pythonPath = this.config.pythonPath ?? 'python';
    const voiceEnginePath = this.config.voiceEnginePath ?? 
      join(process.cwd(), 'src', 'voice-engine', 'apps', 'api');
    
    // Set environment variables
    const env = {
      ...process.env,
      VENICE_API_KEY: this.config.veniceApiKey ?? process.env.VENICE_API_KEY ?? '',
      VOICE_DB_PATH: this.config.dbPath ?? process.env.VOICE_DB_PATH ?? 
        join(process.env.HOME ?? process.env.USERPROFILE ?? '.', '.opencode-sidepanel', 'bridge.db'),
      TTS_PROVIDER: process.env.TTS_PROVIDER ?? 'local',
      TTS_MODEL_ID: process.env.TTS_MODEL_ID ?? 'qwen3-tts-customvoice',
      TTS_DEVICE: process.env.TTS_DEVICE ?? 'cuda:0',
      STT_PROVIDER: process.env.STT_PROVIDER ?? 'mock',
      PORT: this.port.toString(),
    };

    logger.info('Starting voice engine service', {
      pythonPath,
      voiceEnginePath,
      port: this.port,
    });

    // Spawn Python process using uvicorn directly
    // Path: apps/api/src/main.py
    const mainModule = 'apps.api.src.main:app';
    this.process = spawn(pythonPath, [
      '-m', 'uvicorn',
      mainModule,
      '--host', '0.0.0.0',
      '--port', this.port.toString(),
      '--log-level', 'info',
    ], {
      cwd: join(voiceEnginePath, '..', '..', '..'),  // Go to voice-engine root
      env,
      stdio: ['ignore', 'pipe', 'pipe'],
    });

    // Log stdout
    this.process.stdout?.on('data', (data) => {
      logger.info('Voice service stdout', { data: data.toString() });
    });

    // Log stderr
    this.process.stderr?.on('data', (data) => {
      logger.error('Voice service stderr', { data: data.toString() });
    });

    // Handle process exit
    this.process.on('exit', (code) => {
      logger.warn('Voice service exited', { code });
      this.process = null;
    });

    // Wait for service to be ready
    await this.waitForReady();
    
    logger.info('Voice engine service started', { baseUrl: this.baseUrl });
  }

  /**
   * Wait for service to be ready
   */
  private async waitForReady(maxAttempts = 30): Promise<void> {
    for (let i = 0; i < maxAttempts; i++) {
      try {
        const response = await fetch(`${this.baseUrl}/health`);
        if (response.ok) {
          return;
        }
      } catch {
        // Service not ready yet
      }
      await new Promise(resolve => setTimeout(resolve, 1000));
    }
    throw new Error('Voice service failed to start');
  }

  /**
   * Stop voice service
   */
  async stop(): Promise<void> {
    if (this.process) {
      logger.info('Stopping voice service');
      this.process.kill('SIGTERM');
      this.process = null;
    }
  }

  /**
   * Get base URL for voice API
   */
  getBaseUrl(): string {
    return this.baseUrl;
  }

  /**
   * Proxy request to voice service
   */
  async proxyRequest(path: string, options: RequestInit = {}): Promise<Response> {
    const url = `${this.baseUrl}${path}`;
    return fetch(url, options);
  }
}
