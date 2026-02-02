// File Context FFI Implementation - ES Module
// Stub implementation for compilation

// Helper: Explicit default value
const explicitDefault = (value, defaultValue) => {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
};

// In-memory storage for stub
const contextFiles = new Map();

// Estimate tokens
const estimateTokens = (content) => {
  if (!content || content.length === 0) return 0;
  return Math.max(1, Math.ceil(content.length / 4));
};

// Get language from path
const getLanguageFromPath = (filePath) => {
  const ext = filePath.substring(filePath.lastIndexOf('.'));
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
  return explicitDefault(langMap[ext], "text");
};

export const addFileToContext = (store) => (filePath) => (sessionId) => () => {
  const sessionKey = explicitDefault(sessionId, "default");
  const tokens = 100; // Stub estimate
  
  if (!contextFiles.has(sessionKey)) {
    contextFiles.set(sessionKey, []);
  }
  
  contextFiles.get(sessionKey).push({
    path: filePath,
    tokens: tokens,
    status: "in-context",
    language: getLanguageFromPath(filePath)
  });
  
  return {
    tag: "Right",
    value: {
      success: true,
      tokens: tokens,
      contextBudget: {
        used: tokens,
        total: 1000000
      }
    }
  };
};

export const getContextFiles = (store) => (sessionId) => (filter) => () => {
  const sessionKey = explicitDefault(sessionId, "default");
  const files = contextFiles.get(sessionKey) || [];
  
  return {
    files: files,
    contextBudget: {
      used: files.reduce((sum, f) => sum + f.tokens, 0),
      total: 1000000
    }
  };
};

export const readFileContent = (filePath) => () => {
  // Stub: return empty content
  return {
    tag: "Right",
    value: ""
  };
};
