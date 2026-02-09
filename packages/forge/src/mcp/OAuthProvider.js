// Forge.MCP.OAuthProvider FFI
// OAuth URL construction and token exchange for MCP server authentication

// Build OAuth authorization URL with proper encoding
export const buildAuthUrlFFI = (authUrl) => (clientId) => (scopes) => (state) => {
  const params = [
    'client_id=' + encodeURIComponent(clientId),
    'redirect_uri=' + encodeURIComponent('http://localhost:8765/oauth/callback'),
    'scope=' + encodeURIComponent(scopes.join(' ')),
    'state=' + encodeURIComponent(state),
    'response_type=code'
  ];
  return authUrl + '?' + params.join('&');
};

// Exchange authorization code for access token
export const exchangeCodeFFI = (tokenUrl) => (clientId) => (clientSecret) => (code) => () => {
  return new Promise((resolve) => {
    try {
      const body = new URLSearchParams({
        grant_type: 'authorization_code',
        code: code,
        client_id: clientId,
        redirect_uri: 'http://localhost:8765/oauth/callback'
      });
      if (clientSecret) {
        body.set('client_secret', clientSecret);
      }

      fetch(tokenUrl, {
        method: 'POST',
        headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
        body: body.toString()
      }).then((response) => {
        if (!response.ok) {
          return response.text().then((errorText) => {
            resolve({ tag: 'Left', value: 'Token exchange failed: ' + response.status + ' ' + errorText });
          });
        }
        return response.json().then((data) => {
          if (!data.access_token) {
            resolve({ tag: 'Left', value: 'No access_token in response' });
            return;
          }
          resolve({ tag: 'Right', value: data.access_token });
        });
      }).catch((err) => {
        resolve({ tag: 'Left', value: 'Token exchange request failed: ' + err.message });
      });
    } catch (err) {
      resolve({ tag: 'Left', value: err.message });
    }
  });
};
