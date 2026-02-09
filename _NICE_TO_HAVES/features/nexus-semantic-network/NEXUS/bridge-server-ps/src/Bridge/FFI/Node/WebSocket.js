// WebSocket Server FFI (ws library)
"use strict";

var WebSocket = require("ws");

exports.createServer = function(options) {
  return function() {
    var wss = new WebSocket.Server({
      server: options.server,
      path: options.path
    });
    return wss;
  };
};

exports.onConnection = function(wss) {
  return function(handler) {
    return function() {
      wss.on("connection", function(ws) {
        handler(ws)();
      });
    };
  };
};

exports.send = function(ws) {
  return function(message) {
    return function() {
      ws.send(message);
    };
  };
};

exports.onMessage = function(ws) {
  return function(handler) {
    return function() {
      ws.on("message", function(data) {
        handler(data.toString())();
      });
    };
  };
};

exports.onClose = function(ws) {
  return function(handler) {
    return function() {
      ws.on("close", function(code, reason) {
        handler(code)(reason.toString())();
      });
    };
  };
};

exports.onError = function(ws) {
  return function(handler) {
    return function() {
      ws.on("error", function(error) {
        handler(error.message)();
      });
    };
  };
};

exports.closeConnection = function(ws) {
  return function(code) {
    return function(reason) {
      return function() {
        ws.close(code, reason);
      };
    };
  };
};
