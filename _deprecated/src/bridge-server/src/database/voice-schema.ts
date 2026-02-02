/**
 * Voice Engine Database Schema
 * 
 * SQLite schema extensions for voice chat functionality.
 * Integrated with Bridge Server database.
 */

import Database from 'better-sqlite3';

/**
 * Initialize voice engine tables in database
 */
export function initializeVoiceTables(db: Database.Database): void {
  // Voice chat sessions table
  db.exec(`
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
  db.exec(`
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
  db.exec(`
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
}
