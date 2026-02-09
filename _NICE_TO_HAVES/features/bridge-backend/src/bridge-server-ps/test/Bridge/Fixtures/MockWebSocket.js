// Mock WebSocket FFI Implementation
"use strict";

exports.modify_ = function(f) {
  return function(ref) {
    return function() {
      var current = ref.value;
      ref.value = f(current);
    };
  };
};

exports.createMockServer = function() {
  return {
    connections: []
  };
};

exports.addConnection = function(server) {
  return function(id) {
    return function() {
      var messages = [];
      var connected = true;
      var conn = {
        id: id,
        messages: messages,
        connected: connected
      };
      server.connections.push(conn);
      return conn;
    };
  };
};

exports.sendToConnection = function(conn) {
  return function(message) {
    return function() {
      if (conn.connected) {
        conn.messages.push(message);
      }
    };
  };
};

exports.broadcast = function(server) {
  return function(message) {
    return function() {
      server.connections.forEach(function(conn) {
        if (conn.connected) {
          conn.messages.push(message);
        }
      });
    };
  };
};
