// State Synchronization Integration Tests FFI Implementation
"use strict";

exports.createMockClient = function(id) {
  return function() {
    var messages = { value: [] };
    var connected = { value: true };
    return {
      id: id,
      receivedMessages: messages,
      connected: connected
    };
  };
};

exports.createMultipleClients = function(count) {
  return function() {
    var clients = [];
    for (var i = 0; i < count; i++) {
      var messages = { value: [] };
      var connected = { value: true };
      clients.push({
        id: "client-" + i,
        receivedMessages: messages,
        connected: connected
      });
    }
    return clients;
  };
};

exports.subscribeToStateChanges = function(store) {
  return function(client) {
    return function() {
      // Subscribe to state changes via notifyListeners
      // This is a simplified mock - in real implementation would use onStateChange
      var listener = function(path, value) {
        return function() {
          if (client.connected.value) {
            var current = client.receivedMessages.value;
            client.receivedMessages.value = current.concat([JSON.stringify({ path: path, value: value })]);
          }
        };
      };
      
      // Add listener to store (simplified - would use proper API)
      if (!store._testListeners) {
        store._testListeners = [];
      }
      store._testListeners.push(listener);
      
      // Store unsubscribe function
      client.unsubscribe = function() {
        if (store._testListeners) {
          var index = store._testListeners.indexOf(listener);
          if (index > -1) {
            store._testListeners.splice(index, 1);
          }
        }
      };
    };
  };
};

exports.disconnectClient = function(client) {
  return function() {
    client.connected.value = false;
    if (client.unsubscribe) {
      client.unsubscribe();
    }
  };
};

exports.shouldBeGreaterThanOrEqual = function(a) {
  return function(b) {
    return a >= b;
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
