// File Context FFI Implementation
// Tracks files in context for each session using SQLite database
// Uses context_files table for persistence
"use strict";

// Helper: Explicit default value (replaces banned || pattern)
function explicitDefault(value, defaultValue) {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
}

const Database = require("better-sqlite3");
const crypto = require("crypto");
const fs = require("fs");
const path = require("path");

// Get database path from environment (same as bridge server)
function getDatabasePath() {
  const storagePath = process.env.STORAGE_PATH !== undefined && process.env.STORAGE_PATH !== null ? process.env.STORAGE_PATH : "./bridge.db";
  return storagePath;
}

// Open database connection (lazy, cached)
let dbConnection = null;
function getDatabase() {
  if (!dbConnection) {
    const dbPath = getDatabasePath();
    dbConnection = new Database(dbPath);
    
    // Ensure context_files table exists
    dbConnection.exec(`
      CREATE TABLE IF NOT EXISTS context_files (
        id TEXT PRIMARY KEY,
        session_id TEXT NOT NULL,
        path TEXT NOT NULL,
        relative_path TEXT NOT NULL,
        language TEXT,
        tokens INTEGER NOT NULL,
        status TEXT NOT NULL DEFAULT 'in-context' CHECK (status IN ('reading', 'in-context', 'stale', 'removed')),
        source TEXT NOT NULL DEFAULT 'user-added' CHECK (source IN ('user-added', 'ai-read', 'ai-written', 'preset')),
        added_at TEXT NOT NULL DEFAULT (datetime('now')),
        last_read_at TEXT,
        last_referenced_at TEXT,
        content_hash TEXT,
        UNIQUE(session_id, path)
      );
      CREATE INDEX IF NOT EXISTS idx_context_files_session ON context_files(session_id);
    `);
  }
  return dbConnection;
}

// Calculate content hash (SHA-256)
function calculateContentHash(content) {
  return crypto.createHash("sha256").update(content, "utf8").digest("hex");
}

// Get relative path from absolute path
function getRelativePath(filePath) {
  try {
    const cwd = process.cwd();
    return path.relative(cwd, filePath);
  } catch (e) {
    return filePath;
  }
}

// Estimate tokens (improved estimation)
// Uses language-aware estimation: code files typically have more tokens per char than prose
// TODO: Replace with actual tokenizer (e.g., tiktoken, @anthropic-ai/tokenizer, or gpt-tokenizer)
// For now, uses improved estimation based on content characteristics
function estimateTokens(content) {
  if (content === undefined || content === null || content.length === 0) {
    return 0;
  }
  
  // Base estimation: ~4 chars per token
  // Code files tend to have more tokens per char due to:
  // - More whitespace/punctuation
  // - Shorter identifiers
  // - More special characters
  
  // Detect if content looks like code (heuristic)
  const codeIndicators = [
    /^\s*(function|class|import|export|const|let|var|def|module|type|data)/m,
    /[{}();=<>\[\]]/,
    /^\s*\/\//,
    /^\s*#/,
    /^\s*\/\*/,
  ];
  
  const isCode = codeIndicators.some(pattern => pattern.test(content));
  
  // Code: ~3.5 chars per token (more tokens)
  // Prose: ~4 chars per token (standard)
  const charsPerToken = isCode ? 3.5 : 4.0;
  
  return Math.max(1, Math.ceil(content.length / charsPerToken));
}

exports.addFileToContext = function(store) {
  return function(filePath) {
    return function(sessionId) {
      return function() {
        try {
          const db = getDatabase();
          const sessionKey = sessionId !== undefined && sessionId !== null ? sessionId : "default";
          
          // Read file content
          let content = "";
          let tokens = 0;
          let contentHash = null;
          try {
            content = fs.readFileSync(filePath, "utf8");
            tokens = estimateTokens(content);
            contentHash = calculateContentHash(content);
          } catch (e) {
            // File doesn't exist or can't be read
            tokens = 100; // Default estimate
            contentHash = null;
          }
          
          const relativePath = getRelativePath(filePath);
          const language = getLanguageFromPath(filePath);
          const fileSize = getFileSize(filePath);
          const now = new Date().toISOString();
          const fileId = crypto.randomUUID();
          
          // Check if file already exists for this session
          const existingStmt = db.prepare("SELECT * FROM context_files WHERE session_id = ? AND path = ?");
          const existing = existingStmt.get(sessionKey, filePath);
          
          if (existing) {
            // Update existing record
            const updateStmt = db.prepare(`
              UPDATE context_files 
              SET tokens = ?, last_read_at = ?, last_referenced_at = ?, content_hash = ?, status = 'in-context'
              WHERE session_id = ? AND path = ?
            `);
            updateStmt.run(tokens, now, now, contentHash, sessionKey, filePath);
            
            // Calculate total tokens for session
            const totalStmt = db.prepare("SELECT SUM(tokens) as total FROM context_files WHERE session_id = ?");
            const totalResult = totalStmt.get(sessionKey);
            const totalTokens = totalResult !== undefined && totalResult !== null && totalResult.total !== undefined && totalResult.total !== null ? totalResult.total : 0;
            
            return {
              tag: "Right",
              value: {
                success: true,
                tokens: tokens,
                contextBudget: {
                  used: totalTokens,
                  total: 1000000 // Default context window (1M tokens)
                }
              }
            };
          }
          
          // Insert new record
          const insertStmt = db.prepare(`
            INSERT INTO context_files (
              id, session_id, path, relative_path, language, tokens, 
              status, source, added_at, last_read_at, last_referenced_at, content_hash
            ) VALUES (?, ?, ?, ?, ?, ?, 'in-context', 'user-added', ?, ?, ?, ?)
          `);
          insertStmt.run(
            fileId, sessionKey, filePath, relativePath, language, tokens,
            now, now, now, contentHash
          );
          
          // Calculate total tokens for session
          const totalStmt = db.prepare("SELECT SUM(tokens) as total FROM context_files WHERE session_id = ?");
          const totalResult = totalStmt.get(sessionKey);
          const totalTokens = totalResult !== undefined && totalResult !== null && totalResult.total !== undefined && totalResult.total !== null ? totalResult.total : 0;
          
          return {
            tag: "Right",
            value: {
              success: true,
              tokens: tokens,
              contextBudget: {
                used: totalTokens,
                total: 1000000 // Default context window (1M tokens)
              }
            }
          };
        } catch (e) {
          return {
            tag: "Left",
            value: "Failed to add file to context: " + e.message
          };
        }
      };
    };
  };
};

// | Get context files
exports.getContextFiles = function(store) {
  return function(sessionId) {
    return function(filter) {
      return function() {
        try {
          const db = getDatabase();
          const sessionKey = sessionId !== undefined && sessionId !== null ? sessionId : "default";
          
          // Build query with optional filter
          let query = "SELECT * FROM context_files WHERE session_id = ?";
          const params = [sessionKey];
          
          if (filter !== undefined && filter !== null && filter.trim() !== "") {
            query += " AND (path LIKE ? OR relative_path LIKE ?)";
            const filterPattern = "%" + filter + "%";
            params.push(filterPattern, filterPattern);
          }
          
          query += " ORDER BY added_at DESC";
          
          const stmt = db.prepare(query);
          const rows = stmt.all.apply(stmt, params);
          
          // Transform database rows to FileInContext format
          const files = rows.map(row => ({
            path: row.path,
            tokens: row.tokens,
            readAt: row.last_read_at ? new Date(row.last_read_at).getTime() : new Date(row.added_at).getTime(),
            status: row.status,
            language: explicitDefault(row.language, "text"),
            size: 0 // Size not stored in DB, would need to read file
          }));
          
          // Calculate total tokens
          const totalStmt = db.prepare("SELECT SUM(tokens) as total FROM context_files WHERE session_id = ?");
          const totalResult = totalStmt.get(sessionKey);
          const totalTokens = totalResult !== undefined && totalResult !== null && totalResult.total !== undefined && totalResult.total !== null ? totalResult.total : 0;
          
          return {
            files: files,
            contextBudget: {
              used: totalTokens,
              total: 1000000 // Default context window (1M tokens)
            }
          };
        } catch (e) {
          return {
            files: [],
            contextBudget: {
              used: 0,
              total: 1000000
            }
          };
        }
      };
    };
  };
};

// Helper functions
function getLanguageFromPath(filePath) {
  const ext = require("path").extname(filePath);
  const langMap = {
    ".js": "javascript",
    ".ts": "typescript",
    ".purs": "purescript",
    ".hs": "haskell",
    ".lean": "lean",
    ".md": "markdown",
    ".json": "json",
    ".yaml": "yaml",
    ".yml": "yaml"
  };
  return langMap[ext] !== undefined && langMap[ext] !== null ? langMap[ext] : "text";
}

function getFileSize(filePath) {
  try {
    const fs = require("fs");
    const stats = fs.statSync(filePath);
    return stats.size;
  } catch (e) {
    return 0;
  }
}

// | Read file content
exports.readFileContent = function(filePath) {
  return function() {
    try {
      const content = fs.readFileSync(filePath, "utf8");
      return {
        tag: "Right",
        value: content
      };
    } catch (e) {
      return {
        tag: "Left",
        value: "Failed to read file: " + e.message
      };
    }
  };
};
