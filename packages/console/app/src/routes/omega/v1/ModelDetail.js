// Omega V1 Model Detail Route FFI
// Wraps omega handler with Google format

import { handler } from "../util/Handler.js";

export const handleModelDetailPOST = async (event) => {
  const url = event.request.url;
  return handler(event, {
    format: "google",
    parseApiKey: (headers) => headers.get("x-goog-api-key") ?? undefined,
    parseModel: (url, body) => {
      const parts = url.split("/");
      const lastPart = parts[parts.length - 1];
      const modelPart = lastPart?.split(":")?.[0];
      return modelPart ?? "";
    },
    parseIsStream: (url, body) => {
      const parts = url.split("/");
      const lastPart = parts[parts.length - 1];
      const streamPart = lastPart?.split(":")?.[1];
      return streamPart?.startsWith("streamGenerateContent") ?? false;
    },
  });
};

export const extractModelFromUrl = (url) => {
  const parts = url.split("/");
  const lastPart = parts[parts.length - 1];
  const modelPart = lastPart?.split(":")?.[0];
  return modelPart || "";
};

export const isStreamUrl = (url) => {
  const parts = url.split("/");
  const lastPart = parts[parts.length - 1];
  const streamPart = lastPart?.split(":")?.[1];
  return streamPart?.startsWith("streamGenerateContent") ?? false;
};

export const getHeaderFromForeign = (headers, name) => {
  const value = headers.get(name);
  return value === null ? null : value;
};
