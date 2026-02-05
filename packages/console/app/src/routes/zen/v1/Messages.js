// Omega V1 Messages Route FFI
// Wraps omega handler with Anthropic format

import { handler } from "../util/Handler.js";

export const handleMessagesPOST = async (event) => {
  return handler(event, {
    format: "anthropic",
    parseApiKey: (headers) => headers.get("x-api-key") ?? undefined,
    parseModel: (url, body) => body.model,
    parseIsStream: (url, body) => !!body.stream,
  });
};

export const getBodyModel = (body) => {
  return body.model || "";
};

export const getBodyStream = (body) => {
  return !!body.stream;
};

export const getHeaderFromForeign = (headers, name) => {
  const value = headers.get(name);
  return value === null ? null : value;
};
