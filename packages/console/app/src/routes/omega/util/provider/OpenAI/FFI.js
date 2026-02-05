// OpenAI Provider FFI
// JavaScript implementations for OpenAI provider functions
// FULL DETERMINISM - NO ??, ?., lazy &&, undefined, null without explicit handling
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/openai.ts
// Migrated: 2026-02-04

let usageStore = null;

// Modify headers (mutates Headers object stored in globalThis._currentHeadersObj)
// Called from PureScript modifyHeaders function via FFI
export function modifyHeadersImpl(bodyJson, apiKey) {
  const headers = globalThis._currentHeadersObj;
  if (typeof headers !== "object" || headers === null || !(headers instanceof Headers)) {
    return;
  }
  headers.set("authorization", `Bearer ${apiKey}`);
}

// Parse usage from chunk
export function parseUsageImpl(chunk) {
  const lines = chunk.split("\n");
  const event = lines[0];
  const data = lines[1];
  if (typeof event !== "string" || event !== "event: response.completed") return;
  if (typeof data !== "string" || data.length < 6 || data.substring(0, 6) !== "data: ") return;

  try {
    const json = JSON.parse(data.slice(6));
    if (typeof json !== "object" || json === null) return;
    const jsonResponse = json.response;
    if (typeof jsonResponse === "object" && jsonResponse !== null) {
      const jsonResponseUsage = jsonResponse.usage;
      if (typeof jsonResponseUsage === "object" && jsonResponseUsage !== null) {
        usageStore = jsonResponseUsage;
      }
    }
  } catch (e) {
    return;
  }
}

// Retrieve usage
export function retrieveUsageImpl() {
  if (usageStore === null || typeof usageStore === "undefined") {
    return null;
  }
  try {
    return JSON.stringify(usageStore);
  } catch (e) {
    return null;
  }
}

// Parse usage JSON
export function parseUsageJson(usageJson) {
  try {
    const u = JSON.parse(usageJson);
    if (typeof u !== "object" || u === null) {
      return { inputTokens: null, outputTokens: null, reasoningTokens: null, cacheReadTokens: null };
    }

    const uInputTokens = u.input_tokens;
    const uOutputTokens = u.output_tokens;
    const inputTokens = typeof uInputTokens === "number" ? uInputTokens : null;
    const outputTokens = typeof uOutputTokens === "number" ? uOutputTokens : null;

    const uOutputTokensDetails = u.output_tokens_details;
    let reasoningTokens = null;
    if (typeof uOutputTokensDetails === "object" && uOutputTokensDetails !== null) {
      const reasoningTokensValue = uOutputTokensDetails.reasoning_tokens;
      if (typeof reasoningTokensValue === "number") {
        reasoningTokens = reasoningTokensValue;
      }
    }

    const uInputTokensDetails = u.input_tokens_details;
    let cacheReadTokens = null;
    if (typeof uInputTokensDetails === "object" && uInputTokensDetails !== null) {
      const cachedTokensValue = uInputTokensDetails.cached_tokens;
      if (typeof cachedTokensValue === "number") {
        cacheReadTokens = cachedTokensValue;
      }
    }

    return {
      inputTokens,
      outputTokens,
      reasoningTokens,
      cacheReadTokens,
    };
  } catch {
    return { inputTokens: null, outputTokens: null, reasoningTokens: null, cacheReadTokens: null };
  }
}

// Convert message to input format
export function convertMessageToInput(msgJson) {
  try {
    const msg = JSON.parse(msgJson);
    return JSON.stringify(msg);
  } catch {
    return null;
  }
}

// Convert message from OpenAI format
export function convertMessage(msgJson) {
  try {
    const m = JSON.parse(msgJson);
    return JSON.stringify(m);
  } catch {
    return null;
  }
}

// Get messages array
export function getMessages(bodyJson) {
  try {
    const body = JSON.parse(bodyJson);
    if (typeof body !== "object" || body === null) {
      return [];
    }
    const bodyInput = body.input;
    const bodyMessages = body.messages;
    const msgs = Array.isArray(bodyInput) ? bodyInput : (Array.isArray(bodyMessages) ? bodyMessages : []);
    return msgs.map((m) => JSON.stringify(m));
  } catch {
    return [];
  }
}

// Parse stop sequences
export function parseStop(bodyJson) {
  try {
    const body = JSON.parse(bodyJson);
    if (typeof body !== "object" || body === null) {
      return null;
    }
    const bodyStopSequences = body.stop_sequences;
    const bodyStop = body.stop;
    const v = bodyStopSequences !== null && typeof bodyStopSequences !== "undefined" ? bodyStopSequences : bodyStop;
    if (v === null || typeof v === "undefined") return null;
    if (Array.isArray(v)) return JSON.stringify(v.length === 1 ? [v[0]] : v);
    if (typeof v === "string") return JSON.stringify([v]);
    return null;
  } catch {
    return null;
  }
}

// Convert stop
export function convertStop(stopJson) {
  if (stopJson === null || typeof stopJson === "undefined") return null;
  try {
    const stop = typeof stopJson === "string" ? JSON.parse(stopJson) : stopJson;
    if (Array.isArray(stop)) return JSON.stringify(stop);
    if (typeof stop === "string") return JSON.stringify([stop]);
    return null;
  } catch {
    return null;
  }
}

// Parse tool choice
export function parseToolChoice(bodyJson) {
  try {
    const body = JSON.parse(bodyJson);
    if (typeof body !== "object" || body === null) {
      return null;
    }
    const tc = body.tool_choice;
    if (tc === null || typeof tc === "undefined") return null;
    if (tc === "auto") return JSON.stringify({ type: "auto" });
    if (tc === "required") return JSON.stringify({ type: "required" });
    if (typeof tc === "object" && tc !== null && typeof tc.type === "string" && tc.type === "function") {
      const tcFunction = tc.function;
      if (typeof tcFunction === "object" && tcFunction !== null && typeof tcFunction.name === "string" && tcFunction.name.length > 0) {
        return JSON.stringify({ type: "function", function: { name: tcFunction.name } });
      }
    }
    return null;
  } catch {
    return null;
  }
}

// Convert tool choice
export function convertToolChoice(tcJson) {
  if (tcJson === null || typeof tcJson === "undefined") return null;
  try {
    const tc = typeof tcJson === "string" ? JSON.parse(tcJson) : tcJson;
    if (typeof tc !== "object" || tc === null) {
      return null;
    }
    if (typeof tc.type === "string" && tc.type === "auto") return JSON.stringify("auto");
    if (typeof tc.type === "string" && tc.type === "required") return JSON.stringify("required");
    if (typeof tc.type === "string" && tc.type === "function") {
      const tcFunction = tc.function;
      if (typeof tcFunction === "object" && tcFunction !== null && typeof tcFunction.name === "string" && tcFunction.name.length > 0) {
        return JSON.stringify({ type: "function", function: { name: tcFunction.name } });
      }
    }
    return null;
  } catch {
    return null;
  }
}

// Convert tools
export function convertTools(toolsJson) {
  if (toolsJson === null || typeof toolsJson === "undefined") return null;
  try {
    const tools = typeof toolsJson === "string" ? JSON.parse(toolsJson) : toolsJson;
    if (!Array.isArray(tools)) return null;
    const converted = tools.map((tool) => {
      if (typeof tool === "object" && tool !== null && typeof tool.type === "string" && tool.type === "function") {
        const toolFunction = tool.function;
        return {
          type: "function",
          name: typeof toolFunction === "object" && toolFunction !== null ? toolFunction.name : null,
          description: typeof toolFunction === "object" && toolFunction !== null ? toolFunction.description : null,
          parameters: typeof toolFunction === "object" && toolFunction !== null ? toolFunction.parameters : null,
          strict: typeof toolFunction === "object" && toolFunction !== null ? toolFunction.strict : null,
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
    if (typeof obj !== "object" || obj === null) {
      return typeof defaultValue === "string" ? defaultValue : JSON.stringify(defaultValue);
    }
    const value = obj[key];
    if (value === null || typeof value === "undefined") {
      return typeof defaultValue === "string" ? defaultValue : JSON.stringify(defaultValue);
    }
    return typeof value === "string" ? value : JSON.stringify(value);
  } catch {
    return typeof defaultValue === "string" ? defaultValue : JSON.stringify(defaultValue);
  }
}

// Get field maybe
export function getFieldMaybe(objJson, key) {
  try {
    const obj = JSON.parse(objJson);
    if (typeof obj !== "object" || obj === null) {
      return null;
    }
    const value = obj[key];
    if (value === null || typeof value === "undefined") {
      return null;
    }
    return JSON.stringify(value);
  } catch {
    return null;
  }
}

// Has choices array
export function hasChoicesArray(respJson) {
  try {
    const resp = JSON.parse(respJson);
    if (typeof resp !== "object" || resp === null) {
      return false;
    }
    return Array.isArray(resp.choices);
  } catch {
    return false;
  }
}

// Parse common response
export function parseCommonResponse(respJson) {
  return respJson;
}

// Convert from OpenAI format
export function convertFromOpenaiFormat(respJson) {
  try {
    const resp = JSON.parse(respJson);
    if (typeof resp !== "object" || resp === null) {
      return respJson;
    }
    const respResponse = resp.response;
    const r = typeof respResponse === "object" && respResponse !== null ? respResponse : resp;
    return JSON.stringify(r);
  } catch {
    return respJson;
  }
}

// Convert choices to output
export function convertChoicesToOutput(choicesJson) {
  try {
    const choices = JSON.parse(choicesJson);
    return JSON.stringify(choices);
  } catch {
    return JSON.stringify([]);
  }
}

// Convert finish reason
export function convertFinishReason(choicesJson) {
  try {
    const choices = JSON.parse(choicesJson);
    if (!Array.isArray(choices) || choices.length === 0) return null;
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
  if (usageJson === null || typeof usageJson === "undefined") return null;
  try {
    const u = JSON.parse(usageJson);
    if (typeof u !== "object" || u === null) {
      return null;
    }
    const uPromptTokensDetails = u.prompt_tokens_details;
    const cachedTokens = typeof uPromptTokensDetails === "object" && uPromptTokensDetails !== null && typeof uPromptTokensDetails.cached_tokens === "number" ? uPromptTokensDetails.cached_tokens : null;

    const result = {
      input_tokens: typeof u.prompt_tokens === "number" ? u.prompt_tokens : 0,
      output_tokens: typeof u.completion_tokens === "number" ? u.completion_tokens : 0,
      total_tokens: typeof u.total_tokens === "number" ? u.total_tokens : 0,
    };
    if (cachedTokens !== null) {
      result.input_tokens_details = { cached_tokens: cachedTokens };
    }
    return JSON.stringify(result);
  } catch {
    return null;
  }
}

// Parse chunk data
export function parseChunkData(dataLine) {
  if (typeof dataLine !== "string" || dataLine.length < 6 || dataLine.substring(0, 6) !== "data: ") return null;
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
    if (typeof json !== "object" || json === null) {
      return JSON.stringify({ id: "", object: "chat.completion.chunk", created: Math.floor(Date.now() / 1000), model: "", choices: [] });
    }
    const e = eventLineStr.replace("event: ", "").trim();
    const jsonResponse = json.response;
    const respObj = typeof jsonResponse === "object" && jsonResponse !== null ? jsonResponse : {};

    const respObjId = respObj.id;
    const jsonId = json.id;
    const idValue = typeof respObjId === "string" && respObjId.length > 0 ? respObjId : (typeof jsonId === "string" && jsonId.length > 0 ? jsonId : "");

    const respObjModel = respObj.model;
    const jsonModel = json.model;
    const modelValue = typeof respObjModel === "string" && respObjModel.length > 0 ? respObjModel : (typeof jsonModel === "string" && jsonModel.length > 0 ? jsonModel : "");

    return JSON.stringify({
      id: idValue,
      object: "chat.completion.chunk",
      created: Math.floor(Date.now() / 1000),
      model: modelValue,
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
    if (typeof choice !== "object" || choice === null) {
      return "";
    }
    const d = choice.delta;
    if (typeof d !== "object" || d === null) return "";

    if (typeof d.content === "string" && d.content.length > 0) {
      const data = {
        id,
        type: "response.output_text.delta",
        delta: d.content,
        response: { id, model },
      };
      return `event: response.output_text.delta\ndata: ${JSON.stringify(data)}`;
    }

    if (Array.isArray(d.tool_calls)) {
      for (const tc of d.tool_calls) {
        if (typeof tc === "object" && tc !== null) {
          const tcFunction = tc.function;
          if (typeof tcFunction === "object" && tcFunction !== null && typeof tcFunction.name === "string" && tcFunction.name.length > 0) {
            const data = {
              type: "response.output_item.added",
              output_index: 0,
              item: {
                id: tc.id,
                type: "function_call",
                name: tcFunction.name,
                call_id: tc.id,
                arguments: "",
              },
            };
            return `event: response.output_item.added\ndata: ${JSON.stringify(data)}`;
          }
          if (typeof tcFunction === "object" && tcFunction !== null && typeof tcFunction.arguments === "string" && tcFunction.arguments.length > 0) {
            const data = {
              type: "response.function_call_arguments.delta",
              output_index: 0,
              delta: tcFunction.arguments,
            };
            return `event: response.function_call_arguments.delta\ndata: ${JSON.stringify(data)}`;
          }
        }
      }
    }

    if (typeof choice.finish_reason === "string" && choice.finish_reason.length > 0) {
      const u = chunk.usage;
      let usageResult = null;
      if (typeof u === "object" && u !== null) {
        const promptTokensValue = typeof u.prompt_tokens === "number" ? u.prompt_tokens : 0;
        const completionTokensValue = typeof u.completion_tokens === "number" ? u.completion_tokens : 0;
        const totalTokensValue = typeof u.total_tokens === "number" ? u.total_tokens : 0;

        const uPromptTokensDetails = u.prompt_tokens_details;
        const cachedTokens = typeof uPromptTokensDetails === "object" && uPromptTokensDetails !== null && typeof uPromptTokensDetails.cached_tokens === "number" ? uPromptTokensDetails.cached_tokens : null;

        usageResult = {
          input_tokens: promptTokensValue,
          output_tokens: completionTokensValue,
          total_tokens: totalTokensValue,
        };
        if (cachedTokens !== null) {
          usageResult.input_tokens_details = { cached_tokens: cachedTokens };
        }
      }

      const data = {
        id,
        type: "response.completed",
        response: { id, model },
      };
      if (usageResult !== null) {
        data.response.usage = usageResult;
      }
      return `event: response.completed\ndata: ${JSON.stringify(data)}`;
    }

    return "";
  } catch {
    return "";
  }
}
