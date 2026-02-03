// Bridge Client WebSocket FFI (ES Module format)

export const createClient = (url) => () => {
  const wsUrl = url.replace(/^http/, "ws") + "/ws";
  return {
    url: wsUrl,
    ws: null,
    connected: false
  };
};

export const connect = (client) => () => {
  return new Promise((resolve) => {
    try {
      client.ws = new WebSocket(client.url);
      
      client.ws.onopen = () => {
        client.connected = true;
        resolve({ tag: "Right", value: {} });
      };
      
      client.ws.onerror = (error) => {
        resolve({ tag: "Left", value: error.message || "Connection failed" });
      };
      
      client.ws.onclose = () => {
        client.connected = false;
      };
    } catch (e) {
      resolve({ tag: "Left", value: e.message || "Failed to create connection" });
    }
  });
};

export const sendEvent = (client) => (eventJson) => () => {
  return new Promise((resolve) => {
    if (!client.connected || !client.ws) {
      resolve({ tag: "Left", value: "Not connected" });
      return;
    }
    
    try {
      const message = {
        jsonrpc: "2.0",
        method: "forge.event",
        params: { event: JSON.parse(eventJson) }
      };
      client.ws.send(JSON.stringify(message));
      resolve({ tag: "Right", value: {} });
    } catch (e) {
      resolve({ tag: "Left", value: e.message || "Send failed" });
    }
  });
};

export const sendMessage = (client) => (messageJson) => () => {
  return new Promise((resolve) => {
    if (!client.connected || !client.ws) {
      resolve({ tag: "Left", value: "Not connected" });
      return;
    }
    
    try {
      const message = {
        jsonrpc: "2.0",
        method: "forge.message",
        params: JSON.parse(messageJson)
      };
      client.ws.send(JSON.stringify(message));
      resolve({ tag: "Right", value: {} });
    } catch (e) {
      resolve({ tag: "Left", value: e.message || "Send failed" });
    }
  });
};

export const sendToolExecution = (client) => (executionJson) => () => {
  return new Promise((resolve) => {
    if (!client.connected || !client.ws) {
      resolve({ tag: "Left", value: "Not connected" });
      return;
    }
    
    try {
      const message = {
        jsonrpc: "2.0",
        method: "forge.tool.execution",
        params: JSON.parse(executionJson)
      };
      client.ws.send(JSON.stringify(message));
      resolve({ tag: "Right", value: {} });
    } catch (e) {
      resolve({ tag: "Left", value: e.message || "Send failed" });
    }
  });
};

export const sendConfig = (client) => (configJson) => () => {
  return new Promise((resolve) => {
    if (!client.connected || !client.ws) {
      resolve({ tag: "Left", value: "Not connected" });
      return;
    }
    
    try {
      const message = {
        jsonrpc: "2.0",
        method: "forge.config",
        params: { config: JSON.parse(configJson) }
      };
      client.ws.send(JSON.stringify(message));
      resolve({ tag: "Right", value: {} });
    } catch (e) {
      resolve({ tag: "Left", value: e.message || "Send failed" });
    }
  });
};
