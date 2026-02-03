// Forge Plugin FFI Implementation (ES Module format)

export const getBridgeUrl = () => () => {
  return new Promise((resolve) => {
    const url = (typeof process !== 'undefined' && process.env?.BRIDGE_SERVER_URL) || "http://localhost:8765";
    resolve(url);
  });
};

export const logError = (msg) => () => {
  return new Promise((resolve) => {
    console.error("[forge-sidepanel-plugin]", msg);
    resolve({});
  });
};

export const logInfo = (msg) => () => {
  return new Promise((resolve) => {
    console.log("[forge-sidepanel-plugin]", msg);
    resolve({});
  });
};

export const emptyHooks = {
  event: null,
  "chat.message": null,
  "tool.execute.after": null,
  config: null
};

export const createHooks = (client) => ({
  event: (input) => () => {
    return new Promise((resolve) => {
      const eventJson = JSON.stringify(input.event);
      Promise.resolve(client.sendEvent(eventJson)()).then(() => {
        resolve({});
      }).catch((err) => {
        console.error("Failed to forward event:", err);
        resolve({});
      });
    });
  },
  "chat.message": (input, output) => () => {
    return new Promise((resolve) => {
      const messageJson = JSON.stringify({
        sessionID: input.sessionID,
        messageID: input.messageID,
        agent: input.agent,
        model: input.model,
        message: output.message,
        parts: output.parts
      });
      Promise.resolve(client.sendMessage(messageJson)()).then(() => {
        resolve({});
      }).catch((err) => {
        console.error("Failed to forward message:", err);
        resolve({});
      });
    });
  },
  "tool.execute.after": (input, output) => () => {
    return new Promise((resolve) => {
      const executionJson = JSON.stringify({
        tool: input.tool,
        sessionID: input.sessionID,
        callID: input.callID,
        title: output.title,
        output: output.output,
        metadata: output.metadata
      });
      Promise.resolve(client.sendToolExecution(executionJson)()).then(() => {
        resolve({});
      }).catch((err) => {
        console.error("Failed to forward tool execution:", err);
        resolve({});
      });
    });
  },
  config: (config) => () => {
    return new Promise((resolve) => {
      const configJson = JSON.stringify(config);
      Promise.resolve(client.sendConfig(configJson)()).then(() => {
        resolve({});
      }).catch((err) => {
        console.error("Failed to forward config:", err);
        resolve({});
      });
    });
  }
});

export const handleEvent = (client) => (input) => () => {
  return new Promise((resolve) => {
    const eventJson = JSON.stringify(input.event);
    Promise.resolve(client.sendEvent(eventJson)()).then(() => {
      resolve({});
    }).catch((err) => {
      console.error("Failed to handle event:", err);
      resolve({});
    });
  });
};

export const handleChatMessage = (client) => (input) => () => {
  return new Promise((resolve) => {
    const messageJson = JSON.stringify({
      sessionID: input.sessionID,
      messageID: input.messageID || null,
      agent: input.agent || null,
      model: input.model || null,
      message: input.message,
      parts: input.parts || []
    });
    Promise.resolve(client.sendMessage(messageJson)()).then(() => {
      resolve({});
    }).catch((err) => {
      console.error("Failed to handle chat message:", err);
      resolve({});
    });
  });
};

export const handleToolExecuteAfter = (client) => (input) => () => {
  return new Promise((resolve) => {
    const executionJson = JSON.stringify({
      tool: input.tool,
      sessionID: input.sessionID,
      callID: input.callID,
      title: input.title,
      output: input.output,
      metadata: input.metadata
    });
    Promise.resolve(client.sendToolExecution(executionJson)()).then(() => {
      resolve({});
    }).catch((err) => {
      console.error("Failed to handle tool execution:", err);
      resolve({});
    });
  });
};

export const handleConfig = (client) => (config) => () => {
  return new Promise((resolve) => {
    const configJson = typeof config === "string" ? config : JSON.stringify(config);
    Promise.resolve(client.sendConfig(configJson)()).then(() => {
      resolve({});
    }).catch((err) => {
      console.error("Failed to handle config:", err);
      resolve({});
    });
  });
};
