// FFI Integration Tests FFI Implementation
"use strict";

exports.getTestDbPath = function() {
  return ":memory:"; // Use in-memory database for tests
};

exports.getTestAnalyticsPath = function() {
  return ":memory:"; // Use in-memory DuckDB for tests
};

exports.generateSnapshotId = function() {
  return "snapshot-" + Date.now() + "-" + Math.random().toString(36).substr(2, 9);
};

exports.getCurrentTimestamp = function() {
  return new Date().toISOString();
};

exports.computeStateHash = function(stateJson) {
  // Simple hash function for state
  var hash = 0;
  for (var i = 0; i < stateJson.length; i++) {
    var char = stateJson.charCodeAt(i);
    hash = ((hash << 5) - hash) + char;
    hash = hash & hash; // Convert to 32bit integer
  }
  return Math.abs(hash).toString(36);
};

exports.shouldBeGreaterThanOrEqual = function(a) {
  return function(b) {
    return a >= b;
  };
};
