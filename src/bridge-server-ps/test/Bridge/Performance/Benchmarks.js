// Performance Benchmarks FFI Implementation
"use strict";

exports.getCurrentTimeMs = function() {
  return function() {
    return performance.now ? performance.now() : Date.now();
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

exports.createMultipleClients = function(count) {
  return function() {
    var clients = [];
    for (var i = 0; i < count; i++) {
      var messages = [];
      var connected = true;
      clients.push({
        id: "client-" + i,
        receivedMessages: { value: messages },
        connected: { value: connected }
      });
    }
    return clients;
  };
};

exports.subscribeToStateChanges = function(store) {
  return function(client) {
    return function() {
      // Simplified subscription
      if (!store._testListeners) {
        store._testListeners = [];
      }
      var listener = function(path, value) {
        return function() {
          if (client.connected.value) {
            var current = client.receivedMessages.value;
            client.receivedMessages.value = current.concat([JSON.stringify({ path: path, value: value })]);
          }
        };
      };
      store._testListeners.push(listener);
    };
  };
};

exports.parseJsonRpcRequest = function(request) {
  return function() {
    try {
      JSON.parse(request);
    } catch (e) {
      // Ignore
    }
  };
};

exports.shouldBeLessThan = function(a) {
  return function(b) {
    return a < b;
  };
};

exports.traverse_ = function(f) {
  return function(arr) {
    return function() {
      for (var i = 0; i < arr.length; i++) {
        f(arr[i])();
      }
    };
  };
};
