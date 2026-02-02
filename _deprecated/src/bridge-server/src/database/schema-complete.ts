/**
 * Database Schema - Complete Implementation
 * SQLite schema for persistent storage
 */
import Database from 'better-sqlite3';
import { randomUUID } from 'crypto';
import pino from 'pino';

const logger = pino({ name: 'database' });

export interface Snapshot {
  id: string;
  timestamp: Date;
  stateHash: string;
  data: Record<string, unknown>;
  trigger?: 'auto' | 'manual' | 'pre-edit';
  description?: string;
}

export interface SessionRecord {
  id: string;
  sessionId: string;
  promptTokens: number;
  completionTokens: number;
  cost: number;
  model: string;
  provider: string;
  startedAt: Date;
  endedAt: Date | null;
}

export interface BalanceHistoryRecord {
  id: string;
  timestamp: Date;
  diem: number;
  usd: number;
  effective: number;
  consumptionRate: number;
  timeToDepletion: number;
}

/**
 * Database Manager - Complete implementation
 */
export class DatabaseManager {
  private db: Database.Database;
  
  constructor(path: string) {
    logger.info('Initializing database', { path });
    this.db = new Database(path);
    this.initializeSchema();
  }
  
  /**
   * Initialize database schema
   */
  private initializeSchema(): void {
    // Initialize voice tables first (before other tables)
    this.initializeVoiceTables();
    
    // Snapshots table
    this.db.exec(`
      CREATE TABLE IF NOT EXISTS snapshots (
        id TEXT PRIMARY KEY,
        timestamp TEXT NOT NULL,
        state_hash TEXT NOT NULL,
        data TEXT NOT NULL,
        trigger TEXT DEFAULT 'auto',
        description TEXT
      );
      
      CREATE INDEX IF NOT EXISTS idx_snapshots_timestamp ON snapshots(timestamp);
      CREATE INDEX IF NOT EXISTS idx_snapshots_state_hash ON snapshots(state_hash);
    `);
    
    // Sessions table
    this.db.exec(`
      CREATE TABLE IF NOT EXISTS sessions (
        id TEXT PRIMARY KEY,
        session_id TEXT NOT NULL,
        prompt_tokens INTEGER NOT NULL,
        completion_tokens INTEGER NOT NULL,
        cost REAL NOT NULL,
        model TEXT NOT NULL,
        provider TEXT NOT NULL,
        started_at TEXT NOT NULL,
        ended_at TEXT
      );
      
      CREATE INDEX IF NOT EXISTS idx_sessions_session_id ON sessions(session_id);
      CREATE INDEX IF NOT EXISTS idx_sessions_started_at ON sessions(started_at);
    `);
    
    // Balance history table
    this.db.exec(`
      CREATE TABLE IF NOT EXISTS balance_history (
        id TEXT PRIMARY KEY,
        timestamp TEXT NOT NULL,
        diem REAL NOT NULL,
        usd REAL NOT NULL,
        effective REAL NOT NULL,
        consumption_rate REAL NOT NULL,
        time_to_depletion INTEGER NOT NULL
      );
      
      CREATE INDEX IF NOT EXISTS idx_balance_history_timestamp ON balance_history(timestamp);
    `);
    
    logger.info('Database schema initialized');
  }
  
  /**
   * Initialize voice engine tables
   */
  private initializeVoiceTables(): void {
    // Voice chat sessions table
    this.db.exec(`
      CREATE TABLE IF NOT EXISTS voice_chat_sessions (
        id TEXT PRIMARY KEY,
        conversation_id TEXT NOT NULL,
        org_id TEXT NOT NULL,
        user_id TEXT NOT NULL,
        config TEXT NOT NULL,
        state TEXT NOT NULL CHECK (state IN ('idle', 'listening', 'processing',
                                          'thinking', 'speaking', 'interrupted', 'error', 'ended')),
        total_audio_seconds REAL NOT NULL DEFAULT 0.0,
        total_stt_tokens INTEGER NOT NULL DEFAULT 0,
        total_tts_characters INTEGER NOT NULL DEFAULT 0,
        started_at TEXT NOT NULL,
        ended_at TEXT
      );
      
      CREATE INDEX IF NOT EXISTS idx_voice_sessions_conversation ON voice_chat_sessions(conversation_id);
      CREATE INDEX IF NOT EXISTS idx_voice_sessions_user ON voice_chat_sessions(user_id);
      CREATE INDEX IF NOT EXISTS idx_voice_sessions_started ON voice_chat_sessions(started_at);
    `);

    // Voice chat messages table
    this.db.exec(`
      CREATE TABLE IF NOT EXISTS voice_chat_messages (
        id TEXT PRIMARY KEY,
        session_id TEXT NOT NULL,
        conversation_id TEXT NOT NULL,
        role TEXT NOT NULL CHECK (role IN ('user', 'assistant')),
        text TEXT NOT NULL,
        audio_url TEXT,
        duration_seconds REAL,
        stt_confidence REAL,
        created_at TEXT NOT NULL,
        FOREIGN KEY (session_id) REFERENCES voice_chat_sessions(id) ON DELETE CASCADE
      );
      
      CREATE INDEX IF NOT EXISTS idx_voice_messages_session ON voice_chat_messages(session_id);
      CREATE INDEX IF NOT EXISTS idx_voice_messages_conversation ON voice_chat_messages(conversation_id);
      CREATE INDEX IF NOT EXISTS idx_voice_messages_created ON voice_chat_messages(created_at);
    `);

    // TTS models registry table
    this.db.exec(`
      CREATE TABLE IF NOT EXISTS tts_models (
        id TEXT PRIMARY KEY,
        hf_repo TEXT NOT NULL UNIQUE,
        model_name TEXT NOT NULL,
        expected_sha TEXT NOT NULL,
        actual_sha TEXT,
        local_path TEXT,
        status TEXT NOT NULL CHECK (status IN ('downloading', 'ready', 'error', 'mismatch')),
        file_size_bytes INTEGER,
        download_date TEXT,
        last_verified_date TEXT,
        error_message TEXT,
        created_at TEXT NOT NULL,
        updated_at TEXT NOT NULL
      );
      
      CREATE INDEX IF NOT EXISTS idx_tts_models_status ON tts_models(status);
      CREATE INDEX IF NOT EXISTS idx_tts_models_repo ON tts_models(hf_repo);
    `);
    
    logger.info('Voice engine tables initialized');
  }
  
  /**
   * Save snapshot
   */
  saveSnapshot(snapshot: Snapshot): string {
    const stmt = this.db.prepare(`
      INSERT INTO snapshots (id, timestamp, state_hash, data, trigger, description)
      VALUES (?, ?, ?, ?, ?, ?)
    `);
    
    stmt.run(
      snapshot.id,
      snapshot.timestamp.toISOString(),
      snapshot.stateHash,
      JSON.stringify(snapshot.data),
      snapshot.trigger ?? 'auto',
      snapshot.description ?? ''
    );
    
    logger.debug('Snapshot saved', { id: snapshot.id });
    return snapshot.id;
  }
  
  /**
   * Get snapshot by ID
   */
  getSnapshot(id: string): Snapshot | null {
    const stmt = this.db.prepare('SELECT * FROM snapshots WHERE id = ?');
    const row = stmt.get(id) as {
      id: string;
      timestamp: string;
      state_hash: string;
      data: string;
      trigger?: string;
      description?: string;
    } | undefined;
    
    if (!row) {
      return null;
    }
    
    return {
      id: row.id,
      timestamp: new Date(row.timestamp),
      stateHash: row.state_hash,
      data: JSON.parse(row.data) as Record<string, unknown>,
      trigger: (row.trigger as 'auto' | 'manual' | 'pre-edit') ?? 'auto',
      description: row.description,
    };
  }
  
  /**
   * List snapshots (most recent first)
   */
  listSnapshots(limit: number = 100): Snapshot[] {
    const stmt = this.db.prepare(`
      SELECT * FROM snapshots
      ORDER BY timestamp DESC
      LIMIT ?
    `);
    
    const rows = stmt.all(limit) as Array<{
      id: string;
      timestamp: string;
      state_hash: string;
      data: string;
      trigger?: string;
      description?: string;
    }>;
    
    return rows.map(row => ({
      id: row.id,
      timestamp: new Date(row.timestamp),
      stateHash: row.state_hash,
      data: JSON.parse(row.data) as Record<string, unknown>,
      trigger: (row.trigger as 'auto' | 'manual' | 'pre-edit') ?? 'auto',
      description: row.description,
    }));
  }
  
  /**
   * Save session
   */
  saveSession(session: SessionRecord): string {
    const stmt = this.db.prepare(`
      INSERT INTO sessions (
        id, session_id, prompt_tokens, completion_tokens, cost,
        model, provider, started_at, ended_at
      )
      VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
    `);
    
    stmt.run(
      session.id,
      session.sessionId,
      session.promptTokens,
      session.completionTokens,
      session.cost,
      session.model,
      session.provider,
      session.startedAt.toISOString(),
      session.endedAt ? session.endedAt.toISOString() : null
    );
    
    logger.debug('Session saved', { id: session.id, sessionId: session.sessionId });
    return session.id;
  }
  
  /**
   * Get session by ID
   */
  getSession(id: string): SessionRecord | null {
    const stmt = this.db.prepare('SELECT * FROM sessions WHERE id = ?');
    const row = stmt.get(id) as {
      id: string;
      session_id: string;
      prompt_tokens: number;
      completion_tokens: number;
      cost: number;
      model: string;
      provider: string;
      started_at: string;
      ended_at: string | null;
    } | undefined;
    
    if (!row) {
      return null;
    }
    
    return {
      id: row.id,
      sessionId: row.session_id,
      promptTokens: row.prompt_tokens,
      completionTokens: row.completion_tokens,
      cost: row.cost,
      model: row.model,
      provider: row.provider,
      startedAt: new Date(row.started_at),
      endedAt: row.ended_at ? new Date(row.ended_at) : null,
    };
  }
  
  /**
   * Get sessions by session ID (all records for a session)
   */
  getSessionsBySessionId(sessionId: string): SessionRecord[] {
    const stmt = this.db.prepare(`
      SELECT * FROM sessions
      WHERE session_id = ?
      ORDER BY started_at DESC
    `);
    
    const rows = stmt.all(sessionId) as Array<{
      id: string;
      session_id: string;
      prompt_tokens: number;
      completion_tokens: number;
      cost: number;
      model: string;
      provider: string;
      started_at: string;
      ended_at: string | null;
    }>;
    
    return rows.map(row => ({
      id: row.id,
      sessionId: row.session_id,
      promptTokens: row.prompt_tokens,
      completionTokens: row.completion_tokens,
      cost: row.cost,
      model: row.model,
      provider: row.provider,
      startedAt: new Date(row.started_at),
      endedAt: row.ended_at ? new Date(row.ended_at) : null,
    }));
  }

  /**
   * Get all sessions (most recent first)
   */
  getAllSessions(limit: number = 100): SessionRecord[] {
    const stmt = this.db.prepare(`
      SELECT * FROM sessions
      ORDER BY started_at DESC
      LIMIT ?
    `);
    
    const rows = stmt.all(limit) as Array<{
      id: string;
      session_id: string;
      prompt_tokens: number;
      completion_tokens: number;
      cost: number;
      model: string;
      provider: string;
      started_at: string;
      ended_at: string | null;
    }>;
    
    return rows.map(row => ({
      id: row.id,
      sessionId: row.session_id,
      promptTokens: row.prompt_tokens,
      completionTokens: row.completion_tokens,
      cost: row.cost,
      model: row.model,
      provider: row.provider,
      startedAt: new Date(row.started_at),
      endedAt: row.ended_at ? new Date(row.ended_at) : null,
    }));
  }
  
  /**
   * Record balance history
   */
  recordBalanceHistory(
    diem: number,
    usd: number,
    effective: number,
    consumptionRate: number,
    timeToDepletion: number
  ): string {
    const id = randomUUID();
    const timestamp = new Date();
    
    const stmt = this.db.prepare(`
      INSERT INTO balance_history (
        id, timestamp, diem, usd, effective,
        consumption_rate, time_to_depletion
      )
      VALUES (?, ?, ?, ?, ?, ?, ?)
    `);
    
    stmt.run(
      id,
      timestamp.toISOString(),
      diem,
      usd,
      effective,
      consumptionRate,
      timeToDepletion
    );
    
    logger.debug('Balance history recorded', { id, diem, effective });
    return id;
  }
  
  /**
   * Get balance history (most recent first)
   */
  getBalanceHistory(limit: number = 100): BalanceHistoryRecord[] {
    const stmt = this.db.prepare(`
      SELECT * FROM balance_history
      ORDER BY timestamp DESC
      LIMIT ?
    `);
    
    const rows = stmt.all(limit) as Array<{
      id: string;
      timestamp: string;
      diem: number;
      usd: number;
      effective: number;
      consumption_rate: number;
      time_to_depletion: number;
    }>;
    
    return rows.map(row => ({
      id: row.id,
      timestamp: new Date(row.timestamp),
      diem: row.diem,
      usd: row.usd,
      effective: row.effective,
      consumptionRate: row.consumption_rate,
      timeToDepletion: row.time_to_depletion,
    }));
  }
  
  /**
   * Save voice session
   */
  saveVoiceSession(session: {
    id: string;
    conversationId: string;
    orgId: string;
    userId: string;
    state: string;
    totalAudioSeconds: number;
    totalSttTokens: number;
    totalTtsCharacters: number;
    startedAt: Date;
    endedAt?: Date;
  }): void {
    const stmt = this.db.prepare(`
      INSERT OR REPLACE INTO voice_chat_sessions (
        id, conversation_id, org_id, user_id, config, state,
        total_audio_seconds, total_stt_tokens, total_tts_characters,
        started_at, ended_at
      ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    `);
    
    stmt.run(
      session.id,
      session.conversationId,
      session.orgId,
      session.userId,
      JSON.stringify({}), // config
      session.state,
      session.totalAudioSeconds,
      session.totalSttTokens,
      session.totalTtsCharacters,
      session.startedAt.toISOString(),
      session.endedAt?.toISOString() || null
    );
  }
  
  /**
   * Save voice message
   */
  saveVoiceMessage(message: {
    id: string;
    sessionId: string;
    conversationId: string;
    role: 'user' | 'assistant';
    text: string;
    audioUrl?: string;
    durationSeconds?: number;
    sttConfidence?: number;
    createdAt: Date;
  }): void {
    const stmt = this.db.prepare(`
      INSERT OR REPLACE INTO voice_chat_messages (
        id, session_id, conversation_id, role, text, audio_url,
        duration_seconds, stt_confidence, created_at
      ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
    `);
    
    stmt.run(
      message.id,
      message.sessionId,
      message.conversationId,
      message.role,
      message.text,
      message.audioUrl || null,
      message.durationSeconds || null,
      message.sttConfidence || null,
      message.createdAt.toISOString()
    );
  }
  
  /**
   * Save multiple voice messages
   */
  saveVoiceMessages(messages: Array<{
    id: string;
    sessionId: string;
    conversationId: string;
    role: 'user' | 'assistant';
    text: string;
    audioUrl?: string;
    durationSeconds?: number;
    sttConfidence?: number;
    createdAt: Date;
  }>): void {
    const stmt = this.db.prepare(`
      INSERT OR REPLACE INTO voice_chat_messages (
        id, session_id, conversation_id, role, text, audio_url,
        duration_seconds, stt_confidence, created_at
      ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
    `);
    
    const insertMany = this.db.transaction((msgs) => {
      for (const msg of msgs) {
        stmt.run(
          msg.id,
          msg.sessionId,
          msg.conversationId,
          msg.role,
          msg.text,
          msg.audioUrl || null,
          msg.durationSeconds || null,
          msg.sttConfidence || null,
          msg.createdAt.toISOString()
        );
      }
    });
    
    insertMany(messages);
  }
  
  /**
   * Save voice session
   */
  saveVoiceSession(session: {
    id: string;
    conversationId: string;
    orgId: string;
    userId: string;
    state: string;
    totalAudioSeconds: number;
    totalSttTokens: number;
    totalTtsCharacters: number;
    startedAt: Date;
    endedAt?: Date;
  }): void {
    const stmt = this.db.prepare(`
      INSERT OR REPLACE INTO voice_chat_sessions (
        id, conversation_id, org_id, user_id, config, state,
        total_audio_seconds, total_stt_tokens, total_tts_characters,
        started_at, ended_at
      ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    `);
    
    stmt.run(
      session.id,
      session.conversationId,
      session.orgId,
      session.userId,
      JSON.stringify({}), // config
      session.state,
      session.totalAudioSeconds,
      session.totalSttTokens,
      session.totalTtsCharacters,
      session.startedAt.toISOString(),
      session.endedAt?.toISOString() || null
    );
  }
  
  /**
   * Save voice message
   */
  saveVoiceMessage(message: {
    id: string;
    sessionId: string;
    conversationId: string;
    role: 'user' | 'assistant';
    text: string;
    audioUrl?: string;
    durationSeconds?: number;
    sttConfidence?: number;
    createdAt: Date;
  }): void {
    const stmt = this.db.prepare(`
      INSERT OR REPLACE INTO voice_chat_messages (
        id, session_id, conversation_id, role, text, audio_url,
        duration_seconds, stt_confidence, created_at
      ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
    `);
    
    stmt.run(
      message.id,
      message.sessionId,
      message.conversationId,
      message.role,
      message.text,
      message.audioUrl || null,
      message.durationSeconds || null,
      message.sttConfidence || null,
      message.createdAt.toISOString()
    );
  }
  
  /**
   * Get voice session by ID
   */
  getVoiceSession(sessionId: string): {
    id: string;
    conversationId: string;
    orgId: string;
    userId: string;
    state: string;
    totalAudioSeconds: number;
    totalSttTokens: number;
    totalTtsCharacters: number;
    startedAt: Date;
    endedAt?: Date;
  } | null {
    const stmt = this.db.prepare(`
      SELECT * FROM voice_chat_sessions WHERE id = ?
    `);
    
    const row = stmt.get(sessionId) as {
      id: string;
      conversation_id: string;
      org_id: string;
      user_id: string;
      state: string;
      total_audio_seconds: number;
      total_stt_tokens: number;
      total_tts_characters: number;
      started_at: string;
      ended_at: string | null;
    } | undefined;
    
    if (!row) return null;
    
    return {
      id: row.id,
      conversationId: row.conversation_id,
      orgId: row.org_id,
      userId: row.user_id,
      state: row.state,
      totalAudioSeconds: row.total_audio_seconds,
      totalSttTokens: row.total_stt_tokens,
      totalTtsCharacters: row.total_tts_characters,
      startedAt: new Date(row.started_at),
      endedAt: row.ended_at ? new Date(row.ended_at) : undefined,
    };
  }
  
  /**
   * Save multiple voice messages
   */
  saveVoiceMessages(messages: Array<{
    id: string;
    sessionId: string;
    conversationId: string;
    role: 'user' | 'assistant';
    text: string;
    audioUrl?: string;
    durationSeconds?: number;
    sttConfidence?: number;
    createdAt: Date;
  }>): void {
    const stmt = this.db.prepare(`
      INSERT OR REPLACE INTO voice_chat_messages (
        id, session_id, conversation_id, role, text, audio_url,
        duration_seconds, stt_confidence, created_at
      ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
    `);
    
    const insertMany = this.db.transaction((msgs) => {
      for (const msg of msgs) {
        stmt.run(
          msg.id,
          msg.sessionId,
          msg.conversationId,
          msg.role,
          msg.text,
          msg.audioUrl || null,
          msg.durationSeconds || null,
          msg.sttConfidence || null,
          msg.createdAt.toISOString()
        );
      }
    });
    
    insertMany(messages);
  }
  
  /**
   * Get voice messages for session
   */
  getVoiceMessages(sessionId: string): Array<{
    id: string;
    sessionId: string;
    conversationId: string;
    role: 'user' | 'assistant';
    text: string;
    audioUrl?: string;
    durationSeconds?: number;
    sttConfidence?: number;
    createdAt: Date;
  }> {
    const stmt = this.db.prepare(`
      SELECT * FROM voice_chat_messages 
      WHERE session_id = ? 
      ORDER BY created_at ASC
    `);
    
    const rows = stmt.all(sessionId) as Array<{
      id: string;
      session_id: string;
      conversation_id: string;
      role: string;
      text: string;
      audio_url: string | null;
      duration_seconds: number | null;
      stt_confidence: number | null;
      created_at: string;
    }>;
    
    return rows.map(row => ({
      id: row.id,
      sessionId: row.session_id,
      conversationId: row.conversation_id,
      role: row.role as 'user' | 'assistant',
      text: row.text,
      audioUrl: row.audio_url || undefined,
      durationSeconds: row.duration_seconds || undefined,
      sttConfidence: row.stt_confidence || undefined,
      createdAt: new Date(row.created_at),
    }));
  }
  
  /**
   * Close database connection
   */
  close(): void {
    logger.info('Closing database connection');
    this.db.close();
  }
}
