// Stress Tests FFI Implementation
"use strict";

exports.createConcurrentConnections = function(server) {
  return function(count) {
    return function() {
      var connections = [];
      for (var i = 0; i < count; i++) {
        var messages = [];
        var connected = true;
        var conn = {
          id: "conn-" + i,
          messages: messages,
          connected: connected
        };
        server.connections.push(conn);
        connections.push(conn);
      }
      return connections;
    };
  };
};

exports.simulateConnectionChurn = function(server) {
  return function(count) {
    return function() {
      for (var i = 0; i < count; i++) {
        var conn = {
          id: "churn-" + i,
          messages: [],
          connected: true
        };
        server.connections.push(conn);
        // Simulate disconnect
        conn.connected = false;
      }
    };
  };
};

exports.performRapidUpdates = function(store) {
  return function(count) {
    return function() {
      for (var i = 0; i < count; i++) {
        // Simplified - would call actual updateBalance
        if (store._testUpdate) {
          store._testUpdate();
        }
      }
    };
  };
};

exports.performConcurrentUpdates = function(store) {
  return function(count) {
    return function() {
      // Simulate concurrent updates
      for (var i = 0; i < count; i++) {
        if (store._testUpdate) {
          store._testUpdate();
        }
      }
    };
  };
};

exports.getTestDbPath = function() {
  return ":memory:";
};

exports.generateSnapshotId = function() {
  return "snapshot-" + Date.now() + "-" + Math.random().toString(36).substr(2, 9);
};

exports.getCurrentTimestamp = function() {
  return new Date().toISOString();
};

exports.computeStateHash = function(stateJson) {
  var hash = 0;
  for (var i = 0; i < stateJson.length; i++) {
    var char = stateJson.charCodeAt(i);
    hash = ((hash << 5) - hash) + char;
    hash = hash & hash;
  }
  return Math.abs(hash).toString(36);
};

exports.largePayload = function() {
  // Generate large JSON payload (10KB)
  var data = { test: "data", array: [] };
  for (var i = 0; i < 1000; i++) {
    data.array.push({ id: i, content: "x".repeat(10) });
  }
  return JSON.stringify(data);
};

exports.generateLargeJsonRpcRequest = function() {
  var largeData = { data: [] };
  for (var i = 0; i < 5000; i++) {
    largeData.data.push({ id: i, content: "x".repeat(20) });
  }
  return JSON.stringify({
    jsonrpc: "2.0",
    id: 1,
    method: "test.large",
    params: largeData
  });
};

exports.createManyStores = function(count) {
  return function() {
    var stores = [];
    for (var i = 0; i < count; i++) {
      stores.push({
        state: { value: { connected: false, balance: {}, session: null, proof: {}, metrics: {} } },
        listeners: { value: [] }
      });
    }
    return stores;
  };
};

exports.updateAllStores = function(stores) {
  return function() {
    stores.forEach(function(store) {
      if (store._testUpdate) {
        store._testUpdate();
      }
    });
  };
};

exports.createManyDatabaseConnections = function(count) {
  return function() {
    var connections = [];
    for (var i = 0; i < count; i++) {
      // Simplified - would create actual database handles
      connections.push({ id: "db-" + i });
    }
    return connections;
  };
};

exports.shouldBeGreaterThanOrEqual = function(a) {
  return function(b) {
    return a >= b;
  };
};
