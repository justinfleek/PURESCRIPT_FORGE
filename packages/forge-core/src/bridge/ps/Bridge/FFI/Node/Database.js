// better-sqlite3 FFI
"use strict";

// Helper: Explicit default value (replaces banned || pattern)
function explicitDefault(value, defaultValue) {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
}

var Database = require("better-sqlite3");
var crypto = require("crypto");

exports.open = function(path) {
  return function() {
    return new Database(path);
  };
};

exports.close = function(db) {
  return function() {
    db.close();
  };
};

exports.exec = function(db) {
  return function(sql) {
    return function() {
      db.exec(sql);
    };
  };
};

exports.prepare = function(db) {
  return function(sql) {
    return function() {
      return db.prepare(sql);
    };
  };
};

exports.run = function(stmt) {
  return function(params) {
    return function() {
      stmt.run.apply(stmt, params);
    };
  };
};

exports.get = function(stmt) {
  return function(params) {
    return function() {
      try {
        var row = stmt.get.apply(stmt, params);
        return row ? { tag: "Right", value: JSON.stringify(row) } : { tag: "Left", value: "No row found" };
      } catch (e) {
        var errorMessage = e.message !== undefined && e.message !== null ? e.message : String(e);
        return { tag: "Left", value: errorMessage };
      }
    };
  };
};

exports.all = function(stmt) {
  return function(params) {
    return function() {
      try {
        var rows = stmt.all.apply(stmt, params);
        return { tag: "Right", value: JSON.stringify(rows) };
      } catch (e) {
        var errorMessage = e.message !== undefined && e.message !== null ? e.message : String(e);
        return { tag: "Left", value: errorMessage };
      }
    };
  };
};

// | Generate UUID
// | For deterministic operations, use generateUUIDFromSeed
exports.randomUUID = function() {
  return function() {
    return crypto.randomUUID();
  };
};

// | Generate deterministic UUID from namespace and seed
// | Uses SHA-256 hash for deterministic UUID-like ID
exports.generateUUIDFromSeed = function(namespace) {
  return function(seed) {
    const crypto = require('crypto');
    const input = namespace + ':' + seed.toString();
    const hash = crypto.createHash('sha256').update(input).digest('hex');
    const uuid = hash.substring(0, 32);
    return uuid.substring(0, 8) + '-' +
           uuid.substring(8, 12) + '-' +
           uuid.substring(12, 16) + '-' +
           uuid.substring(16, 20) + '-' +
           uuid.substring(20, 32);
  };
};
