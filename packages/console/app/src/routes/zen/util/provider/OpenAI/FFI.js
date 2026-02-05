// OpenAI Provider FFI
// JavaScript implementations for OpenAI provider functions
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/openai.ts
// Migrated: 2026-02-04

let usageStore = null;

// Modify headers (mutates Headers object stored in globalThis._currentHeadersObj)
// Called from PureScript modifyHeaders function via FFI
export function modifyHeadersImpl(bodyJson, apiKey) {
  // Get Headers object from global (set by modifyHeadersFFI)
  const headers = globalThis._currentHeadersObj;
  if (!headers || !(headers instanceof Headers)) {
    return; // No headers object available
  }
  
  // Modify headers (OpenAI: set authorization)
  headers.set("authorization", `Bearer ${apiKey}`);
}

// Parse usage from chunk
export function parseUsageImpl(chunk) {
  const [event, data] = chunk.split("\n");
  if (event !== "event: response.completed") return;
  if (!data.startsWith("data: ")) return;

  try {
    const json = JSON.parse(data.slice(6));
    if (json.response?.usage) {
      usageStore = json.response.usage;
    }
  } catch (e) {
    // Ignore parse errors
  }
}

// Retrieve usage
export function retrieveUsageImpl() {
  return usageStore ? JSON.stringify(usageStore) : null;
}

// Parse usage JSON
export function parseUsageJson(usageJson) {
  try {
    const u = JSON.parse(usageJson);
    return {
      inputTokens: u.input_tokens ?? null,
      outputTokens: u.output_tokens ?? null,
      reasoningTokens: u.output_tokens_details?.reasoning_tokens ?? null,
      cacheReadTokens: u.input_tokens_details?.cached_tokens ?? null,
    };
  } catch {
    return { inputTokens: null, outputTokens: null, reasoningTokens: null, cacheReadTokens: null };
  }
}

// Convert message to input format
export function convertMessageToInput(msgJson) {
  try {
    const msg = JSON.parse(msgJson);
    // Complex conversion logic - simplified for now
    return JSON.stringify(msg);
  } catch {
    return null;
  }
}

// Convert message from OpenAI format
export function convertMessage(msgJson) {
  try {
    const m = JSON.parse(msgJson);
    // Complex conversion logic - simplified for now
    return JSON.stringify(m);
  } catch {
    return null;
  }
}

// Get messages array
export function getMessages(bodyJson) {
  try {
    const body = JSON.parse(bodyJson);
    const msgs = body.input || body.messages || [];
    return msgs.map(m => JSON.stringify(m));
  } catch {
    return [];
  }
}

// Parse stop sequences
export function parseStop(bodyJson) {
  try {
    const body = JSON.parse(bodyJson);
    const v = body.stop_sequences ?? body.stop;
    if (!v) return null;
    if (Array.isArray(v)) return JSON.stringify(v.length === 1 ? [v[0]] : v);
    if (typeof v === "string") return JSON.stringify([v]);
    return null;
  } catch {
    return null;
  }
}

// Convert stop
export function convertStop(stopJson) {
  if (!stopJson) return null;
  try {
    const stop = JSON.parse(stopJson);
    return JSON.stringify(Array.isArray(stop) ? stop : [stop]);
  } catch {
    return null;
  }
}

// Parse tool choice
export function parseToolChoice(bodyJson) {
  try {
    const body = JSON.parse(bodyJson);
    const tc = body.tool_choice;
    if (!tc) return null;
    if (tc === "auto") return JSON.stringify({ type: "auto" });
    if (tc === "required") return JSON.stringify({ type: "required" });
    if (tc.type === "function" && tc.function?.name) {
      return JSON.stringify({ type: "function", function: { name: tc.function.name } });
    }
    return null;
  } catch {
    return null;
  }
}

// Convert tool choice
export function convertToolChoice(tcJson) {
  if (!tcJson) return null;
  try {
    const tc = JSON.parse(tcJson);
    if (tc.type === "auto") return JSON.stringify("auto");
    if (tc.type === "required") return JSON.stringify("required");
    if (tc.type === "function" && tc.function?.name) {
      return JSON.stringify({ type: "function", function: { name: tc.function.name } });
    }
    return null;
  } catch {
    return null;
  }
}

// Convert tools
export function convertTools(toolsJson) {
  if (!toolsJson) return null;
  try {
    const tools = JSON.parse(toolsJson);
    if (!Array.isArray(tools)) return null;
    const converted = tools.map(tool => {
      if (tool.type === "function") {
        return {
          type: "function",
          name: tool.function?.name,
          description: tool.function?.description,
          parameters: tool.function?.parameters,
          strict: tool.function?.strict,
        };
      }
      return tool;
    });
    return JSON.stringify(converted);
  } catch {
    return null;
  }
}

// Parse JSON
export function parseJson(jsonStr) {
  return JSON.parse(jsonStr);
}

// Stringify JSON
export function stringifyJson(obj) {
  return JSON.stringify(obj);
}

// Get field
export function getField(objJson, key, defaultValue) {
  try {
    const obj = JSON.parse(objJson);
    return obj[key] ?? defaultValue;
  } catch {
    return defaultValue;
  }
}

// Get field maybe
export function getFieldMaybe(objJson, key) {
  try {
    const obj = JSON.parse(objJson);
    return obj[key] !== undefined ? JSON.stringify(obj[key]) : null;
  } catch {
    return null;
  }
}

// Has choices array
export function hasChoicesArray(respJson) {
  try {
    const resp = JSON.parse(respJson);
    return Array.isArray(resp.choices);
  } catch {
    return false;
  }
}

// Parse common response
export function parseCommonResponse(respJson) {
  return respJson; // Already in CommonResponse format
}

// Convert from OpenAI format
export function convertFromOpenaiFormat(respJson) {
  try {
    const resp = JSON.parse(respJson);
    const r = resp.response ?? resp;
    // Complex conversion - simplified
    return JSON.stringify(r);
  } catch {
    return respJson;
  }
}

// Convert choices to output
export function convertChoicesToOutput(choicesJson) {
  try {
    const choices = JSON.parse(choicesJson);
    // Complex conversion - simplified
    return JSON.stringify(choices);
  } catch {
    return JSON.stringify([]);
  }
}

// Convert finish reason
export function convertFinishReason(choicesJson) {
  try {
    const choices = JSON.parse(choicesJson);
    if (choices.length === 0) return null;
    const reason = choices[0].finish_reason;
    if (reason === "stop") return JSON.stringify("stop");
    if (reason === "tool_calls") return JSON.stringify("tool_call");
    if (reason === "length") return JSON.stringify("max_output_tokens");
    if (reason === "content_filter") return JSON.stringify("content_filter");
    return null;
  } catch {
    return null;
  }
}

// Convert usage
export function convertUsage(usageJson) {
  if (!usageJson) return null;
  try {
    const u = JSON.parse(usageJson);
    return JSON.stringify({
      input_tokens: u.prompt_tokens,
      output_tokens: u.completion_tokens,
      total_tokens: u.total_tokens,
      ...(u.prompt_tokens_details?.cached_tokens
        ? { input_tokens_details: { cached_tokens: u.prompt_tokens_details.cached_tokens } }
        : {}),
    });
  } catch {
    return null;
  }
}

// Parse chunk data
export function parseChunkData(dataLine) {
  if (!dataLine.startsWith("data: ")) return null;
  try {
    return JSON.parse(dataLine.slice(6));
  } catch {
    return null;
  }
}

// Convert chunk JSON
export function convertChunkJson(jsonStr, eventLineStr) {
  try {
    const json = JSON.parse(jsonStr);
    const e = eventLineStr.replace("event: ", "").trim();
    const respObj = json.response ?? {};
    // Complex conversion - simplified
    return JSON.stringify({
      id: respObj.id ?? json.id ?? "",
      object: "chat.completion.chunk",
      created: Math.floor(Date.now() / 1000),
      model: respObj.model ?? json.model ?? "",
      choices: [],
    });
  } catch {
    return JSON.stringify({ id: "", object: "chat.completion.chunk", created: Math.floor(Date.now() / 1000), model: "", choices: [] });
  }
}

// Format chunk
export function formatChunk(chunkJson, id, model, choiceJson) {
  try {
    const chunk = JSON.parse(chunkJson);
    const choice = JSON.parse(choiceJson);
    const d = choice.delta;
    if (!d) return "";

    if (d.content) {
      const data = {
        id,
        type: "response.output_text.delta",
        delta: d.content,
        response: { id, model },
      };
      return `event: response.output_text.delta\ndata: ${JSON.stringify(data)}`;
    }

    if (d.tool_calls) {
      for (const tc of d.tool_calls) {
        if (tc.function?.name) {
          const data = {
            type: "response.output_item.added",
            output_index: 0,
            item: {
              id: tc.id,
              type: "function_call",
              name: tc.function.name,
              call_id: tc.id,
              arguments: "",
            },
          };
          return `event: response.output_item.added\ndata: ${JSON.stringify(data)}`;
        }
        if (tc.function?.arguments) {
          const data = {
            type: "response.function_call_arguments.delta",
            output_index: 0,
            delta: tc.function.arguments,
          };
          return `event: response.function_call_arguments.delta\ndata: ${JSON.stringify(data)}`;
        }
      }
    }

    if (choice.finish_reason) {
      const u = chunk.usage;
      const usage = u
        ? {
            input_tokens: u.prompt_tokens,
            output_tokens: u.completion_tokens,
            total_tokens: u.total_tokens,
            ...(u.prompt_tokens_details?.cached_tokens
              ? { input_tokens_details: { cached_tokens: u.prompt_tokens_details.cached_tokens } }
              : {}),
          }
        : undefined;

      const data = {
        id,
        type: "response.completed",
        response: { id, model, ...(usage ? { usage } : {}) },
      };
      return `event: response.completed\ndata: ${JSON.stringify(data)}`;
    }

    return "";
  } catch {
    return "";
  }
}
