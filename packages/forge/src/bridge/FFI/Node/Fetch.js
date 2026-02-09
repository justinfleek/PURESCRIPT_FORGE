// Fetch API FFI
"use strict";

exports.fetch = function(url) {
  return function(options) {
    return function(onError, onSuccess) {
      try {
        var headers = {};
        options.headers.forEach(function(h) {
          headers[h.key] = h.value;
        });

        var init = {
          method: options.method,
          headers: headers,
        };

        if (options.body !== null && options.body.value0 !== undefined) {
          init.body = options.body.value0;
        }

        globalThis.fetch(url, init).then(function(response) {
          onSuccess({ tag: "Right", value: response });
        }).catch(function(error) {
          var errorMessage = error.message !== undefined && error.message !== null ? error.message : String(error);
          onSuccess({ tag: "Left", value: errorMessage });
        });
      } catch (e) {
        onSuccess({ tag: "Left", value: String(e) });
      }
      return function(cancelError, onCancelError, onCancelSuccess) {
        onCancelSuccess();
      };
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
      if (value !== null && value !== undefined) {
        return { tag: "Just", value: value };
      }
      return { tag: "Nothing" };
    };
  };
};

exports.json = function(response) {
  return function(onError, onSuccess) {
    try {
      response.json().then(function(data) {
        onSuccess({ tag: "Right", value: JSON.stringify(data) });
      }).catch(function(error) {
        var errorMessage = error.message !== undefined && error.message !== null ? error.message : String(error);
        onSuccess({ tag: "Left", value: errorMessage });
      });
    } catch (e) {
      onSuccess({ tag: "Left", value: String(e) });
    }
    return function(cancelError, onCancelError, onCancelSuccess) {
      onCancelSuccess();
    };
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
  return function(onError, onSuccess) {
    try {
      response.text().then(function(content) {
        onSuccess({ tag: "Right", value: content });
      }).catch(function(error) {
        var errorMessage = error.message !== undefined && error.message !== null ? error.message : String(error);
        onSuccess({ tag: "Left", value: errorMessage });
      });
    } catch (e) {
      onSuccess({ tag: "Left", value: String(e) });
    }
    return function(cancelError, onCancelError, onCancelSuccess) {
      onCancelSuccess();
    };
  };
};
