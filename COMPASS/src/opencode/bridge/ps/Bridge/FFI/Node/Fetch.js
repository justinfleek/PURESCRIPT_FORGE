// Fetch API FFI
"use strict";

// Helper: Explicit default value (replaces banned || pattern)
function explicitDefault(value, defaultValue) {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
}

exports.fetch = function(url) {
  return function(options) {
    return function() {
      return new Promise(function(resolve) {
        var headers = new Headers();
        options.headers.forEach(function(h) {
          headers.set(h.key, h.value);
        });
        
        var init = {
          method: options.method,
          headers: headers,
        };
        
        if (options.body) {
          init.body = options.body;
        }
        
        globalThis.fetch(url, init).then(function(response) {
          resolve({ tag: "Right", value: response });
        }).catch(function(error) {
          var errorMessage = error.message !== undefined && error.message !== null ? error.message : String(error);
          resolve({ tag: "Left", value: errorMessage });
        });
      });
    };
  };
};

exports.getHeaders = function(response) {
  return function() {
    return response.headers;
  };
};

exports.getHeader = function(headers) {
  return function(name) {
    return function() {
      var value = headers.get(name);
      return value ? { tag: "Just", value: value } : { tag: "Nothing" };
    };
  };
};

exports.json = function(response) {
  return function() {
    return new Promise(function(resolve) {
      response.json().then(function(data) {
        resolve({ tag: "Right", value: JSON.stringify(data) });
      }).catch(function(error) {
        var errorMessage = error.message !== undefined && error.message !== null ? error.message : String(error);
        resolve({ tag: "Left", value: errorMessage });
      });
    });
  };
};

exports.ok = function(response) {
  return function() {
    return response.ok;
  };
};

exports.status = function(response) {
  return function() {
    return response.status;
  };
};

exports.text = function(response) {
  return function() {
    return new Promise(function(resolve) {
      response.text().then(function(content) {
        resolve({ tag: "Right", value: content });
      }).catch(function(error) {
        var errorMessage = error.message !== undefined && error.message !== null ? error.message : String(error);
        resolve({ tag: "Left", value: errorMessage });
      });
    });
  };
};
