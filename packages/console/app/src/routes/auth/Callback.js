// Auth Callback Route FFI
// Wraps SolidJS Start route handler and OpenAuth client

import { createClient } from "@openauthjs/openauth/client";

let authClientCache = null;

const getAuthClient = (clientID, issuer) => {
  if (!authClientCache || authClientCache.clientID !== clientID) {
    authClientCache = createClient({
      clientID: clientID,
      issuer: issuer,
    });
  }
  return authClientCache;
};

export const authClientExchange = async (clientID, issuer, code) => {
  const client = getAuthClient(clientID, issuer);
  const callbackUrl = `${issuer}/auth/callback`; // Simplified - would get from request
  const result = await client.exchange(code, callbackUrl);
  return {
    err: result.err ? result.err.message : null,
    tokens: result.tokens ? { access: result.tokens.access } : { access: "" },
  };
};

export const authClientDecode = async (clientID, accessToken) => {
  const client = getAuthClient(clientID, "");
  const decoded = client.decode(accessToken, {});
  return {
    err: decoded.err ? decoded.err.message : null,
    subject: decoded.subject ? {
      properties: {
        accountID: decoded.subject.properties.accountID,
        email: decoded.subject.properties.email,
      },
    } : { properties: { accountID: "", email: "" } },
  };
};
