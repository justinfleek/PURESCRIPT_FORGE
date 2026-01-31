// Database E2E Tests FFI Implementation
"use strict";

exports.getTestDbPath = function() {
  return ":memory:"; // Use in-memory database for tests
};

exports.generateSnapshotId = function() {
  return "snapshot-" + Date.now() + "-" + Math.random().toString(36).substr(2, 9);
};

exports.generateSessionId = function() {
  return "session-" + Date.now() + "-" + Math.random().toString(36).substr(2, 9);
};

exports.generateRecordId = function() {
  return "record-" + Date.now() + "-" + Math.random().toString(36).substr(2, 9);
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

exports.encodeState = function(balanceState) {
  return JSON.stringify({
    balance: {
      venice: {
        diem: balanceState.venice.diem,
        usd: balanceState.venice.usd,
        effective: balanceState.venice.effective,
        lastUpdated: balanceState.venice.lastUpdated
      },
      consumptionRate: balanceState.consumptionRate,
      timeToDepletion: balanceState.timeToDepletion,
      todayUsed: balanceState.todayUsed,
      todayStartBalance: balanceState.todayStartBalance,
      resetCountdown: balanceState.resetCountdown,
      alertLevel: balanceState.alertLevel
    }
  });
};

exports.parseSessions = function(sessionsJson) {
  try {
    var sessions = JSON.parse(sessionsJson);
    return Array.isArray(sessions) ? sessions : [];
  } catch (e) {
    return [];
  }
};

exports.parseBalanceHistory = function(historyJson) {
  try {
    var history = JSON.parse(historyJson);
    return Array.isArray(history) ? history : [];
  } catch (e) {
    return [];
  }
};
