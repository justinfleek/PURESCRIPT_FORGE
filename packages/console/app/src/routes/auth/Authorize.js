// Auth Authorize Route FFI
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

export const authClientAuthorize = async (clientID, issuer, callbackUrl) => {
  const client = getAuthClient(clientID, issuer);
  const result = await client.authorize(callbackUrl.toString(), "code");
  return result.url;
};
