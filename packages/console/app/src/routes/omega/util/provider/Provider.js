// Provider Format Conversion FFI
// Routes conversion calls to appropriate provider-specific functions
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/provider.ts
// Migrated: 2026-02-04

import { fromOpenaiRequestImpl, toOpenaiRequestImpl } from "./OpenAI/Request.js";
import { fromOpenaiResponseImpl, toOpenaiResponseImpl } from "./OpenAI/Response.js";
import { fromOpenaiChunkImpl, toOpenaiChunkImpl } from "./OpenAI/Chunk.js";
import { fromAnthropicRequestImpl, toAnthropicRequestImpl } from "./Anthropic/Request.js";
import { fromAnthropicResponseImpl, toAnthropicResponseImpl } from "./Anthropic/Response.js";
import { fromAnthropicChunkImpl, toAnthropicChunkImpl } from "./Anthropic/Chunk.js";
import { fromOaCompatibleRequestImpl, toOaCompatibleRequestImpl } from "./OpenAICompatible/Request.js";
import { fromOaCompatibleResponseImpl, toOaCompatibleResponseImpl } from "./OpenAICompatible/Response.js";
import { fromOaCompatibleChunkImpl, toOaCompatibleChunkImpl } from "./OpenAICompatible/Chunk.js";
import { fromGoogleRequestImpl, toGoogleRequestImpl } from "./Google/Request.js";
import { fromGoogleResponseImpl, toGoogleResponseImpl } from "./Google/Response.js";
import { fromGoogleChunkImpl, toGoogleChunkImpl } from "./Google/Chunk.js";

// Convert request format (PureScript calls this with CommonRequest object)
// Returns CommonRequest object (conversion happens later in modifyBody)
export function convertRequestFormat(fromFormat, toFormat, req) {
  try {
    // req is already a CommonRequest object from PureScript
    // Since we're always working with CommonRequest in PureScript,
    // format conversion is a no-op - the actual conversion to provider
    // format happens in modifyBody
    return req;
  } catch (e) {
    return req; // Return original on error
  }
}

// Convert response format (PureScript calls this with CommonResponse object)
// Converts from provider format to CommonResponse, then to target format
export function convertResponseFormat(fromFormat, toFormat, resp) {
  try {
    // resp is provider-specific format JSON string from HTTP response
    // First convert to CommonResponse
    let commonResp;
    if (fromFormat === "anthropic") {
      commonResp = fromAnthropicResponseImpl(typeof resp === "string" ? resp : JSON.stringify(resp));
    } else if (fromFormat === "openai") {
      commonResp = fromOpenaiResponseImpl(typeof resp === "string" ? resp : JSON.stringify(resp));
    } else if (fromFormat === "oa-compat") {
      commonResp = fromOaCompatibleResponseImpl(typeof resp === "string" ? resp : JSON.stringify(resp));
    } else if (fromFormat === "google") {
      commonResp = fromGoogleResponseImpl(typeof resp === "string" ? resp : JSON.stringify(resp));
    } else {
      // Assume already CommonResponse
      commonResp = typeof resp === "string" ? JSON.parse(resp) : resp;
    }
    
    // Convert from CommonResponse to target format
    if (toFormat === "anthropic") {
      const result = toAnthropicResponseImpl(commonResp);
      return typeof result === "string" ? JSON.parse(result) : result;
    } else if (toFormat === "openai") {
      const result = toOpenaiResponseImpl(commonResp);
      return typeof result === "string" ? JSON.parse(result) : result;
    } else if (toFormat === "oa-compat") {
      const result = toOaCompatibleResponseImpl(commonResp);
      return typeof result === "string" ? JSON.parse(result) : result;
    } else if (toFormat === "google") {
      const result = toGoogleResponseImpl(commonResp);
      return typeof result === "string" ? JSON.parse(result) : result;
    } else {
      return commonResp; // Unknown format, return CommonResponse
    }
  } catch (e) {
    return resp; // Return original on error
  }
}

// Convert chunk format (PureScript calls this with chunk string from stream)
// Converts from provider format to CommonChunk, then to target format
export function convertChunkFormat(fromFormat, toFormat, chunk) {
  try {
    // chunk is provider-specific format string from stream
    // First convert to CommonChunk
    let commonChunk;
    if (fromFormat === "anthropic") {
      commonChunk = fromAnthropicChunkImpl(chunk);
    } else if (fromFormat === "openai") {
      commonChunk = fromOpenaiChunkImpl(chunk);
    } else if (fromFormat === "oa-compat") {
      commonChunk = fromOaCompatibleChunkImpl(chunk);
    } else if (fromFormat === "google") {
      commonChunk = fromGoogleChunkImpl(chunk);
    } else {
      // Assume already CommonChunk JSON string
      commonChunk = typeof chunk === "string" ? JSON.parse(chunk) : chunk;
    }
    
    // Convert from CommonChunk to target format
    if (toFormat === "anthropic") {
      return toAnthropicChunkImpl(commonChunk);
    } else if (toFormat === "openai") {
      return toOpenaiChunkImpl(commonChunk);
    } else if (toFormat === "oa-compat") {
      return toOaCompatibleChunkImpl(commonChunk);
    } else if (toFormat === "google") {
      return toGoogleChunkImpl(commonChunk);
    } else {
      return typeof commonChunk === "string" ? commonChunk : JSON.stringify(commonChunk);
    }
  } catch (e) {
    return typeof chunk === "string" ? chunk : JSON.stringify(chunk);
  }
}
