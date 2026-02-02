// Bridge Client WebSocket FFI
"use strict";

var WebSocket = require("ws");

exports.createClient = function(url) {
  return function() {
    var wsUrl = url.replace(/^http/, "ws") + "/ws";
    return {
      url: wsUrl,
      ws: null,
      connected: false
    };
  };
};

exports.connect = function(client) {
  return function() {
    return new Promise(function(resolve) {
      try {
        client.ws = new WebSocket(client.url);
        
        client.ws.on("open", function() {
          client.connected = true;
          resolve({ tag: "Right", value: {} });
        });
        
        client.ws.on("error", function(error) {
          resolve({ tag: "Left", value: error.message || "Connection failed" });
        });
        
        client.ws.on("close", function() {
          client.connected = false;
        });
      } catch (e) {
        resolve({ tag: "Left", value: e.message || "Failed to create connection" });
      }
    });
  };
};

exports.sendEvent = function(client) {
  return function(eventJson) {
    return function() {
      return new Promise(function(resolve) {
        if (!client.connected || !client.ws) {
          resolve({ tag: "Left", value: "Not connected" });
          return;
        }
        
        try {
          var message = {
            jsonrpc: "2.0",
            method: "opencode.event",
            params: { event: JSON.parse(eventJson) }
          };
          client.ws.send(JSON.stringify(message));
          resolve({ tag: "Right", value: {} });
        } catch (e) {
          resolve({ tag: "Left", value: e.message || "Send failed" });
        }
      });
    };
  };
};

exports.sendMessage = function(client) {
  return function(messageJson) {
    return function() {
      return new Promise(function(resolve) {
        if (!client.connected || !client.ws) {
          resolve({ tag: "Left", value: "Not connected" });
          return;
        }
        
        try {
          var message = {
            jsonrpc: "2.0",
            method: "opencode.message",
            params: JSON.parse(messageJson)
          };
          client.ws.send(JSON.stringify(message));
          resolve({ tag: "Right", value: {} });
        } catch (e) {
          resolve({ tag: "Left", value: e.message || "Send failed" });
        }
      });
    };
  };
};

exports.sendToolExecution = function(client) {
  return function(executionJson) {
    return function() {
      return new Promise(function(resolve) {
        if (!client.connected || !client.ws) {
          resolve({ tag: "Left", value: "Not connected" });
          return;
        }
        
        try {
          var message = {
            jsonrpc: "2.0",
            method: "opencode.tool.execution",
            params: JSON.parse(executionJson)
          };
          client.ws.send(JSON.stringify(message));
          resolve({ tag: "Right", value: {} });
        } catch (e) {
          resolve({ tag: "Left", value: e.message || "Send failed" });
        }
      });
    };
  };
};

exports.sendConfig = function(client) {
  return function(configJson) {
    return function() {
      return new Promise(function(resolve) {
        if (!client.connected || !client.ws) {
          resolve({ tag: "Left", value: "Not connected" });
          return;
        }
        
        try {
          var message = {
            jsonrpc: "2.0",
            method: "opencode.config",
            params: { config: JSON.parse(configJson) }
          };
          client.ws.send(JSON.stringify(message));
          resolve({ tag: "Right", value: {} });
        } catch (e) {
          resolve({ tag: "Left", value: e.message || "Send failed" });
        }
      });
    };
  };
};
