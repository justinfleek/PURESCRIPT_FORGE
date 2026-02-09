// WebSocket FFI implementation
"use strict";

exports.create = function(url) {
  return function() {
    return new WebSocket(url);
  };
};

exports.readyState = function(ws) {
  return function() {
    return ws.readyState;
  };
};

exports.send = function(ws) {
  return function(message) {
    return function() {
      try {
        ws.send(message);
        return { tag: "Right", value: {} };
      } catch (e) {
        return { tag: "Left", value: e.message || String(e) };
      }
    };
  };
};

exports.close = function(ws) {
  return function() {
    ws.close();
  };
};

exports.closeWith = function(ws) {
  return function(code) {
    return function(reason) {
      return function() {
        ws.close(code, reason);
      };
    };
  };
};

exports.onOpen = function(ws) {
  return function(handler) {
    return function() {
      ws.onopen = function() {
        handler();
      };
    };
  };
};

exports.onClose = function(ws) {
  return function(handler) {
    return function() {
      ws.onclose = function(event) {
        handler(event.code)(event.reason || "");
      };
    };
  };
};

exports.onError = function(ws) {
  return function(handler) {
    return function() {
      ws.onerror = function(event) {
        handler(event.message || "WebSocket error");
      };
    };
  };
};

exports.onMessage = function(ws) {
  return function(handler) {
    return function() {
      ws.onmessage = function(event) {
        handler(event.data);
      };
    };
  };
};
