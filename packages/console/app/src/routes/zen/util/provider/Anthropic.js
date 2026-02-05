// Anthropic Provider FFI
// JavaScript implementations for Anthropic provider functions

import { EventStreamCodec } from "@smithy/eventstream-codec";
import { fromUtf8, toUtf8 } from "@smithy/util-utf8";

let usageStore = null;

export function modifyHeadersImpl(isBedrock, isSonnet, bodyJson, apiKey) {
  const headers = globalThis._currentHeadersObj;
  if (!headers || !(headers instanceof Headers)) {
    return;
  }
  
  const body = JSON.parse(bodyJson);
  if (isBedrock) {
    headers.set("Authorization", `Bearer ${apiKey}`);
  } else {
    headers.set("x-api-key", apiKey);
    headers.set("anthropic-version", headers.get("anthropic-version") ?? "2023-06-01");
    if (body.model?.startsWith("claude-sonnet-")) {
      headers.set("anthropic-beta", "context-1m-2025-08-07");
    }
  }
}

export function modifyBodyImpl(isBedrock, isSonnet, bodyJson) {
  const body = JSON.parse(bodyJson);
  if (isBedrock) {
    return JSON.stringify({
      ...body,
      anthropic_version: "bedrock-2023-05-31",
      anthropic_beta: isSonnet ? "context-1m-2025-08-07" : undefined,
      model: undefined,
      stream: undefined,
    });
  } else {
    return JSON.stringify({
      ...body,
      service_tier: "standard_only",
    });
  }
}

export function createBinaryStreamDecoderImpl(isBedrock) {
  if (!isBedrock) return () => null;
  
  const decoder = new TextDecoder();
  const encoder = new TextEncoder();
  const codec = new EventStreamCodec(toUtf8, fromUtf8);
  let buffer = new Uint8Array(0);
  
  return (value) => {
    const newBuffer = new Uint8Array(buffer.length + value.length);
    newBuffer.set(buffer);
    newBuffer.set(value, buffer.length);
    buffer = newBuffer;

    const messages = [];
    while (buffer.length >= 4) {
      const totalLength = new DataView(buffer.buffer, buffer.byteOffset, buffer.byteLength).getUint32(0, false);
      if (buffer.length < totalLength) break;

      try {
        const subView = buffer.subarray(0, totalLength);
        const decoded = codec.decode(subView);
        buffer = buffer.slice(totalLength);

        if (decoded.headers[":message-type"]?.value === "event") {
          const data = decoder.decode(decoded.body, { stream: true });
          const parsedDataResult = JSON.parse(data);
          delete parsedDataResult.p;
          const binary = atob(parsedDataResult.bytes);
          const uint8 = Uint8Array.from(binary, (c) => c.charCodeAt(0));
          const bytes = decoder.decode(uint8);
          const eventName = JSON.parse(bytes).type;
          messages.push([`event: ${eventName}`, "\n", `data: ${bytes}`, "\n\n"].join(""));
        }
      } catch (e) {
        console.log("Error decoding:", e);
        break;
      }
    }
    return encoder.encode(messages.join(""));
  };
}

export function createUsageParserImpl() {
  return {
    parse: (chunk) => {
      const data = chunk.split("\n")[1];
      if (!data?.startsWith("data: ")) return;
      try {
        const json = JSON.parse(data.slice(6));
        const usageUpdate = json.usage ?? json.message?.usage;
        if (!usageUpdate) return;
        usageStore = {
          ...usageStore,
          ...usageUpdate,
          cache_creation: {
            ...usageStore?.cache_creation,
            ...usageUpdate.cache_creation,
          },
          server_tool_use: {
            ...usageStore?.server_tool_use,
            ...usageUpdate.server_tool_use,
          },
        };
      } catch (e) {
        // Ignore
      }
    },
    retrieve: () => {
      return usageStore ? JSON.stringify(usageStore) : null;
    },
  };
}

export function normalizeUsageImpl(usageJson) {
  try {
    const usage = JSON.parse(usageJson);
    return {
      inputTokens: usage.input_tokens ?? 0,
      outputTokens: usage.output_tokens ?? 0,
      reasoningTokens: null,
      cacheReadTokens: usage.cache_read_input_tokens ?? null,
      cacheWrite5mTokens: usage.cache_creation?.ephemeral_5m_input_tokens ?? null,
      cacheWrite1hTokens: usage.cache_creation?.ephemeral_1h_input_tokens ?? null,
    };
  } catch {
    return {
      inputTokens: 0,
      outputTokens: 0,
      reasoningTokens: null,
      cacheReadTokens: null,
      cacheWrite5mTokens: null,
      cacheWrite1hTokens: null,
    };
  }
}

export function encodeURIComponent(str) {
  return encodeURIComponent(str);
}
