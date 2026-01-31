// | FFI JavaScript bindings for Render API client

const fetch = require('node-fetch');

// | Render client
function createRenderClientImpl(apiKey) {
  return { apiKey };
}

// | Get API key
function getApiKey(client) {
  return client.apiKey;
}


// | Make HTTP request
function makeRequest(client, method, url, body) {
  return function(callback) {
    return function() {
      const headers = {
        'Authorization': 'Bearer ' + client.apiKey,
        'Content-Type': 'application/json'
      };
      
      fetch(url, {
        method: method,
        headers: headers,
        body: body || null
      })
      .then(function(res) {
        // Convert response to our Response type
        const response = {
          status: res.status,
          headers: res.headers,
          ok: res.ok
        };
        
        return res.text().then(function(text) {
          response.body = text;
          callback({ tag: 'Right', value: { tag: 'Right', value: response } })();
        });
      })
      .catch(function(err) {
        callback({ tag: 'Right', value: { tag: 'Left', value: err.message } })();
      });
      
      return function(cancel) {
        cancel();
      };
    };
  };
}

// | Get header from response
function getHeader(response, name) {
  return function() {
    const header = response.headers.get(name);
    return header ? { tag: 'Just', value: header } : { tag: 'Nothing' };
  };
}

// | Get body from response
function getBody(response) {
  return function() {
    return response.body || '';
  };
}

// | Check if response is OK
function isOk(response) {
  return function() {
    return response.ok;
  };
}

// | Parse integer
function parseInt(str) {
  const num = Number.parseInt(str, 10);
  return isNaN(num) ? { tag: 'Nothing' } : { tag: 'Just', value: num };
}

// | Exports
exports.createRenderClientImpl = createRenderClientImpl;
exports.getApiKey = getApiKey;
exports.makeRequest = makeRequest;
exports.getHeader = getHeader;
exports.getBody = getBody;
exports.isOk = isOk;
exports.parseInt = parseInt;
