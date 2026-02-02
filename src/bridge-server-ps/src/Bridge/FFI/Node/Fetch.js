// Fetch API FFI - ES Module

// Helper: Explicit default value (replaces banned || pattern)
const explicitDefault = (value, defaultValue) => {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
};

export const fetch = (url) => (options) => () => {
  return new Promise((resolve) => {
    const headers = new Headers();
    if (options.headers) {
      options.headers.forEach((h) => {
        headers.set(h.key, h.value);
      });
    }
    
    const init = {
      method: options.method,
      headers: headers,
    };
    
    if (options.body) {
      init.body = options.body;
    }
    
    globalThis.fetch(url, init).then((response) => {
      resolve({ tag: "Right", value: response });
    }).catch((error) => {
      const errorMessage = error.message !== undefined && error.message !== null ? error.message : String(error);
      resolve({ tag: "Left", value: errorMessage });
    });
  });
};

export const getHeaders = (response) => () => {
  return response.headers;
};

export const getHeader = (headers) => (name) => () => {
  const value = headers.get(name);
  return value !== null ? value : null; // PureScript Maybe
};

export const json = (response) => () => {
  return new Promise((resolve) => {
    response.json().then((data) => {
      resolve({ tag: "Right", value: JSON.stringify(data) });
    }).catch((error) => {
      const errorMessage = error.message !== undefined && error.message !== null ? error.message : String(error);
      resolve({ tag: "Left", value: errorMessage });
    });
  });
};

export const ok = (response) => () => {
  return response.ok;
};

export const status = (response) => () => {
  return response.status;
};
