// better-sqlite3 FFI - ES Module

// Helper: Explicit default value (replaces banned || pattern)
const explicitDefault = (value, defaultValue) => {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
};

// Note: In real implementation, this would use better-sqlite3
// For now, stub implementation for compilation

let Database = null;

export const open = (path) => () => {
  // Stub: return mock database object
  return {
    _path: path,
    _statements: new Map(),
    close: () => {},
    exec: (sql) => {},
    prepare: (sql) => ({ sql, _db: path })
  };
};

export const close = (db) => () => {
  if (db && db.close) db.close();
};

export const exec = (db) => (sql) => () => {
  if (db && db.exec) db.exec(sql);
};

export const prepare = (db) => (sql) => () => {
  return {
    sql,
    _db: db,
    run: (...args) => {},
    get: (...args) => null,
    all: (...args) => []
  };
};

export const run = (stmt) => (params) => () => {
  if (stmt && stmt.run) {
    stmt.run.apply(stmt, params);
  }
};

export const get = (stmt) => (params) => () => {
  try {
    const row = stmt && stmt.get ? stmt.get.apply(stmt, params) : null;
    return row 
      ? { tag: "Right", value: JSON.stringify(row) } 
      : { tag: "Left", value: "No row found" };
  } catch (e) {
    const errorMessage = e.message !== undefined && e.message !== null ? e.message : String(e);
    return { tag: "Left", value: errorMessage };
  }
};

export const all = (stmt) => (params) => () => {
  try {
    const rows = stmt && stmt.all ? stmt.all.apply(stmt, params) : [];
    return { tag: "Right", value: JSON.stringify(rows) };
  } catch (e) {
    const errorMessage = e.message !== undefined && e.message !== null ? e.message : String(e);
    return { tag: "Left", value: errorMessage };
  }
};

// | Generate UUID
export const randomUUID = () => {
  if (typeof crypto !== 'undefined' && crypto.randomUUID) {
    return crypto.randomUUID();
  }
  // Fallback UUID generation
  return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, (c) => {
    const r = Math.random() * 16 | 0;
    const v = c === 'x' ? r : (r & 0x3 | 0x8);
    return v.toString(16);
  });
};

// | Generate deterministic UUID from namespace and seed
export const generateUUIDFromSeed = (namespace) => (seed) => {
  // Simple hash-based deterministic ID
  const input = namespace + ':' + seed.toString();
  let hash = 0;
  for (let i = 0; i < input.length; i++) {
    const char = input.charCodeAt(i);
    hash = ((hash << 5) - hash) + char;
    hash = hash & hash;
  }
  const hex = Math.abs(hash).toString(16).padStart(32, '0');
  return hex.substring(0, 8) + '-' +
         hex.substring(8, 12) + '-' +
         hex.substring(12, 16) + '-' +
         hex.substring(16, 20) + '-' +
         hex.substring(20, 32);
};
