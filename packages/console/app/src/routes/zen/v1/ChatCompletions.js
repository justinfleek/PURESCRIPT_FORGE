// Omega V1 Chat Completions Route FFI
// Wraps omega handler with OpenAI-compatible format

import { handler } from "../util/Handler.js";

export const handleChatCompletionsPOST = async (event) => {
  return handler(event, {
    format: "oa-compat",
    parseApiKey: (headers) => {
      const auth = headers.get("authorization");
      if (!auth) return undefined;
      const parts = auth.split(" ");
      return parts.length > 1 ? parts[1] : undefined;
    },
    parseModel: (url, body) => body.model,
    parseIsStream: (url, body) => !!body.stream,
  });
};

export const extractBearerToken = (header) => {
  const parts = header.split(" ");
  return parts.length > 1 ? parts[1] : null;
};

export const getBodyModel = (body) => {
  return body.model || "";
};

export const getBodyStream = (body) => {
  return !!body.stream;
};

export const getHeader = (headers, name) => {
  const value = headers.get(name);
  return value === null ? null : value;
};

export const extractBearerTokenFromHeaders = (headers) => {
  const auth = headers.get("authorization");
  if (!auth) return null;
  const parts = auth.split(" ");
  return parts.length > 1 ? parts[1] : null;
};
