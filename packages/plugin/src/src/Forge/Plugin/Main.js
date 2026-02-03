// Forge Plugin FFI Implementation
"use strict";

var process = require("process");

exports.getBridgeUrl = function() {
  return function() {
    return new Promise(function(resolve) {
      var url = process.env.BRIDGE_SERVER_URL || "http://localhost:8765";
      resolve(url);
    });
  };
};

exports.logError = function(msg) {
  return function() {
    return new Promise(function(resolve) {
      console.error("[forge-sidepanel-plugin]", msg);
      resolve({});
    });
  };
};

exports.logInfo = function(msg) {
  return function() {
    return new Promise(function(resolve) {
      console.log("[forge-sidepanel-plugin]", msg);
      resolve({});
    });
  };
};

exports.emptyHooks = {
  event: null,
  "chat.message": null,
  "tool.execute.after": null,
  config: null
};

exports.createHooks = function(client) {
  return {
    event: function(input) {
      return function() {
        return new Promise(function(resolve) {
          var eventJson = JSON.stringify(input.event);
          client.sendEvent(eventJson).then(function(result) {
            resolve({});
          }).catch(function(err) {
            console.error("Failed to forward event:", err);
            resolve({});
          });
        });
      };
    },
    "chat.message": function(input, output) {
      return function() {
        return new Promise(function(resolve) {
          var messageJson = JSON.stringify({
            sessionID: input.sessionID,
            messageID: input.messageID,
            agent: input.agent,
            model: input.model,
            message: output.message,
            parts: output.parts
          });
          client.sendMessage(messageJson).then(function(result) {
            resolve({});
          }).catch(function(err) {
            console.error("Failed to forward message:", err);
            resolve({});
          });
        });
      };
    },
    "tool.execute.after": function(input, output) {
      return function() {
        return new Promise(function(resolve) {
          var executionJson = JSON.stringify({
            tool: input.tool,
            sessionID: input.sessionID,
            callID: input.callID,
            title: output.title,
            output: output.output,
            metadata: output.metadata
          });
          client.sendToolExecution(executionJson).then(function(result) {
            resolve({});
          }).catch(function(err) {
            console.error("Failed to forward tool execution:", err);
            resolve({});
          });
        });
      };
    },
    config: function(config) {
      return function() {
        return new Promise(function(resolve) {
          var configJson = JSON.stringify(config);
          client.sendConfig(configJson).then(function(result) {
            resolve({});
          }).catch(function(err) {
            console.error("Failed to forward config:", err);
            resolve({});
          });
        });
      };
    }
  };
};

// Additional FFI functions declared in Main.purs
exports.handleEvent = function(client) {
  return function(input) {
    return function() {
      return new Promise(function(resolve) {
        var eventJson = JSON.stringify(input.event);
        client.sendEvent(eventJson).then(function(result) {
          resolve({});
        }).catch(function(err) {
          console.error("Failed to handle event:", err);
          resolve({});
        });
      });
    };
  };
};

exports.handleChatMessage = function(client) {
  return function(input) {
    return function() {
      return new Promise(function(resolve) {
        var messageJson = JSON.stringify({
          sessionID: input.sessionID,
          messageID: input.messageID || null,
          agent: input.agent || null,
          model: input.model || null,
          message: input.message,
          parts: input.parts || []
        });
        client.sendMessage(messageJson).then(function(result) {
          resolve({});
        }).catch(function(err) {
          console.error("Failed to handle chat message:", err);
          resolve({});
        });
      });
    };
  };
};

exports.handleToolExecuteAfter = function(client) {
  return function(input) {
    return function() {
      return new Promise(function(resolve) {
        var executionJson = JSON.stringify({
          tool: input.tool,
          sessionID: input.sessionID,
          callID: input.callID,
          title: input.title,
          output: input.output,
          metadata: input.metadata
        });
        client.sendToolExecution(executionJson).then(function(result) {
          resolve({});
        }).catch(function(err) {
          console.error("Failed to handle tool execution:", err);
          resolve({});
        });
      });
    };
  };
};

exports.handleConfig = function(client) {
  return function(config) {
    return function() {
      return new Promise(function(resolve) {
        var configJson = typeof config === "string" ? config : JSON.stringify(config);
        client.sendConfig(configJson).then(function(result) {
          resolve({});
        }).catch(function(err) {
          console.error("Failed to handle config:", err);
          resolve({});
        });
      });
    };
  };
};
