// Terminal Execution FFI Implementation - ES Module

// Helper: Explicit default value (replaces banned || pattern)
const explicitDefault = (value, defaultValue) => {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
};

// Parse command properly (handles quoted strings, escaped characters)
const parseCommand = (cmdStr) => {
  const parts = [];
  let current = '';
  let inQuotes = false;
  let quoteChar = null;
  let escapeNext = false;
  
  for (let i = 0; i < cmdStr.length; i++) {
    const char = cmdStr[i];
    
    if (escapeNext) {
      current += char;
      escapeNext = false;
      continue;
    }
    
    if (char === '\\') {
      escapeNext = true;
      continue;
    }
    
    if ((char === '"' || char === "'") && !inQuotes) {
      inQuotes = true;
      quoteChar = char;
      continue;
    }
    
    if (char === quoteChar && inQuotes) {
      inQuotes = false;
      quoteChar = null;
      continue;
    }
    
    if (char === ' ' && !inQuotes) {
      if (current.length > 0) {
        parts.push(current);
        current = '';
      }
      continue;
    }
    
    current += char;
  }
  
  if (current.length > 0) {
    parts.push(current);
  }
  
  return parts;
};

// | Execute terminal command
export const executeCommand = (command) => (cwd) => (sessionId) => (onError, onSuccess) => () => {
  // Stub implementation for browser/compilation
  // In real Node.js, this would use child_process.spawn
  const cwdPath = explicitDefault(cwd, '.');
  
  console.log(`Executing command: ${command} in ${cwdPath}`);
  
  // Simulate async command execution
  setTimeout(() => {
    onSuccess({
      success: true,
      output: `Stub output for: ${command}`,
      exitCode: 0
    })();
  }, 100);
  
  return (cancelError, cancelerError, cancelerSuccess) => {
    cancelerSuccess()();
  };
};
