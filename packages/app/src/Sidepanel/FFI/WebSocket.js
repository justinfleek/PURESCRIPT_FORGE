// WebSocket FFI implementation

export const create = function(url) {
  return function() {
    return new WebSocket(url);
  };
};

export const readyState = function(ws) {
  return function() {
    return ws.readyState;
  };
};

export const send = function(ws) {
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

export const close = function(ws) {
  return function() {
    ws.close();
  };
};

export const closeWith = function(ws) {
  return function(code) {
    return function(reason) {
      return function() {
        ws.close(code, reason);
      };
    };
  };
};

export const onOpen = function(ws) {
  return function(handler) {
    return function() {
      ws.onopen = function() {
        handler();
      };
    };
  };
};

export const onClose = function(ws) {
  return function(handler) {
    return function() {
      ws.onclose = function(event) {
        handler(event.code)(event.reason || "");
      };
    };
  };
};

export const onError = function(ws) {
  return function(handler) {
    return function() {
      ws.onerror = function(event) {
        handler(event.message || "WebSocket error");
      };
    };
  };
};

export const onMessage = function(ws) {
  return function(handler) {
    return function() {
      ws.onmessage = function(event) {
        handler(event.data);
      };
    };
  };
};
