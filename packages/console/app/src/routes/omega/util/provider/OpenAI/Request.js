// OpenAI Request Conversion FFI
// Full implementation of fromOpenaiRequest and toOpenaiRequest
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/openai.ts
// Migrated: 2026-02-04

// Convert image part to common format
// Returns null for PureScript Maybe (not undefined)
function toImg(p) {
  if (!p || typeof p !== "object") return null;
  if (p.type === "image_url" && p.image_url) {
    return { type: "image_url", image_url: p.image_url };
  }
  if (p.type === "input_image" && p.image_url) {
    return { type: "image_url", image_url: p.image_url };
  }
  const s = p.source;
  if (!s || typeof s !== "object") return null;
  if (s.type === "url" && typeof s.url === "string") {
    return { type: "image_url", image_url: { url: s.url } };
  }
  if (s.type === "base64" && typeof s.media_type === "string" && typeof s.data === "string") {
    return {
      type: "image_url",
      image_url: { url: `data:${s.media_type};base64,${s.data}` },
    };
  }
  return null;
}

// Convert message from OpenAI format to CommonMessage
export function convertMessage(msgJson) {
  try {
    const m = JSON.parse(msgJson);
    if (!m) return null;

    // Responses API items without role
    if (!m.role && m.type) {
      if (m.type === "function_call") {
        const name = m.name;
        const a = m.arguments;
        const args = typeof a === "string" ? a : (typeof a === "object" && a !== null ? JSON.stringify(a) : JSON.stringify({}));
        return JSON.stringify({
          role: "assistant",
          tool_calls: [{ id: m.id, type: "function", function: { name, arguments: args } }],
        });
      }
      if (m.type === "function_call_output") {
        const id = m.call_id;
        const out = m.output;
        const content = typeof out === "string" ? out : JSON.stringify(out);
        return JSON.stringify({ role: "tool", tool_call_id: id, content });
      }
      return null;
    }

    if (m.role === "system" || m.role === "developer") {
      const c = m.content;
      if (typeof c === "string" && c.length > 0) {
        return JSON.stringify({ role: "system", content: c });
      }
      if (Array.isArray(c)) {
        const t = c.find((p) => p && typeof p.text === "string");
        if (t && typeof t.text === "string" && t.text.length > 0) {
          return JSON.stringify({ role: "system", content: t.text });
        }
      }
      return null;
    }

    if (m.role === "user") {
      const c = m.content;
      if (typeof c === "string") {
        return JSON.stringify({ role: "user", content: c });
      } else if (Array.isArray(c)) {
        const parts = [];
        for (const p of c) {
          if (!p || !p.type) continue;
          if ((p.type === "text" || p.type === "input_text") && typeof p.text === "string") {
            parts.push({ type: "text", text: p.text });
          }
          const ip = toImg(p);
          if (ip) parts.push(ip);
          if (p.type === "tool_result") {
            const id = p.tool_call_id;
            const content = typeof p.content === "string" ? p.content : JSON.stringify(p.content);
            // This creates a separate tool message, not part of user content
            // We'll handle this separately
          }
        }
        if (parts.length === 1 && parts[0].type === "text") {
          return JSON.stringify({ role: "user", content: parts[0].text });
        } else if (parts.length > 0) {
          return JSON.stringify({ role: "user", content: parts });
        }
      }
      return null;
    }

    if (m.role === "assistant") {
      const c = m.content;
      const out = { role: "assistant" };
      if (typeof c === "string" && c.length > 0) out.content = c;
      if (Array.isArray(m.tool_calls)) out.tool_calls = m.tool_calls;
      return JSON.stringify(out);
    }

    if (m.role === "tool") {
      return JSON.stringify({
        role: "tool",
        tool_call_id: m.tool_call_id,
        content: m.content,
      });
    }

    return null;
  } catch (e) {
    return null;
  }
}

// Convert CommonMessage to OpenAI input format
export function convertMessageToInput(msgJson) {
  try {
    const m = JSON.parse(msgJson);
    if (!m || !m.role) return null;

    if (m.role === "system") {
      const c = m.content;
      if (typeof c === "string") {
        return JSON.stringify({ role: "system", content: c });
      }
      return null;
    }

    if (m.role === "user") {
      const c = m.content;
      if (typeof c === "string") {
        return JSON.stringify({ role: "user", content: [{ type: "input_text", text: c }] });
      } else if (Array.isArray(c)) {
        const parts = [];
        for (const p of c) {
          const op = toPart(p);
          if (op) parts.push(op);
        }
        if (parts.length > 0) {
          return JSON.stringify({ role: "user", content: parts });
        }
      }
      return null;
    }

    if (m.role === "assistant") {
      const c = m.content;
      if (typeof c === "string" && c.length > 0) {
        return JSON.stringify({ role: "assistant", content: [{ type: "output_text", text: c }] });
      }
      if (Array.isArray(m.tool_calls)) {
        // Tool calls are handled separately as function_call items
        // Return null here, tool calls will be added as separate items
        return null;
      }
      return null;
    }

    if (m.role === "tool") {
      const out = typeof m.content === "string" ? m.content : JSON.stringify(m.content);
      return JSON.stringify({ type: "function_call_output", call_id: m.tool_call_id, output: out });
    }

    return null;
  } catch (e) {
    return null;
  }
}

// Convert content part to OpenAI input part
function toPart(p) {
  if (!p || typeof p !== "object") return null;
  if (p.type === "text" && typeof p.text === "string") {
    return { type: "input_text", text: p.text };
  }
  if (p.type === "image_url" && p.image_url) {
    return { type: "input_image", image_url: p.image_url };
  }
  const s = p.source;
  if (!s || typeof s !== "object") return null;
  if (s.type === "url" && typeof s.url === "string") {
    return { type: "input_image", image_url: { url: s.url } };
  }
  if (s.type === "base64" && typeof s.media_type === "string" && typeof s.data === "string") {
    return {
      type: "input_image",
      image_url: { url: `data:${s.media_type};base64,${s.data}` },
    };
  }
  return null;
}

// Get messages array from body
export function getMessages(bodyJson) {
  try {
    const body = typeof bodyJson === "string" ? JSON.parse(bodyJson) : bodyJson;
    const inMsgs = Array.isArray(body.input) ? body.input : Array.isArray(body.messages) ? body.messages : [];
    return inMsgs.map((m) => JSON.stringify(m));
  } catch (e) {
    return [];
  }
}

// Parse stop sequences
export function parseStop(bodyJson) {
  try {
    const body = typeof bodyJson === "string" ? JSON.parse(bodyJson) : bodyJson;
    const v = body.stop_sequences !== null && typeof body.stop_sequences !== "undefined" ? body.stop_sequences : body.stop;
    if (!v) return null;
    if (Array.isArray(v)) {
      return JSON.stringify(v.length === 1 ? v[0] : v);
    }
    if (typeof v === "string") {
      return JSON.stringify(v);
    }
    return null;
  } catch (e) {
    return null;
  }
}

// Convert stop to stop_sequences format
export function convertStop(stopJson) {
  if (!stopJson) return null;
  try {
    const stop = typeof stopJson === "string" ? JSON.parse(stopJson) : stopJson;
    if (Array.isArray(stop)) {
      return JSON.stringify(stop);
    }
    if (typeof stop === "string") {
      return JSON.stringify([stop]);
    }
    return null;
  } catch (e) {
    return null;
  }
}

// Parse tool choice
export function parseToolChoice(bodyJson) {
  try {
    const body = typeof bodyJson === "string" ? JSON.parse(bodyJson) : bodyJson;
    const tc = body.tool_choice;
    if (!tc) return null;
    if (tc === "auto") {
      return JSON.stringify({ type: "auto" });
    }
    if (tc === "required") {
      return JSON.stringify({ type: "required" });
    }
    if (typeof tc === "object" && tc !== null && typeof tc.type === "string" && tc.type === "function") {
      const tcFunction = tc.function;
      if (typeof tcFunction === "object" && tcFunction !== null && typeof tcFunction.name === "string" && tcFunction.name.length > 0) {
        return JSON.stringify({ type: "function", function: { name: tcFunction.name } });
      }
    }
    return null;
  } catch (e) {
    return null;
  }
}

// Convert tool choice
export function convertToolChoice(tcJson) {
  if (!tcJson) return null;
  try {
    const tc = typeof tcJson === "string" ? JSON.parse(tcJson) : tcJson;
    if (typeof tc === "object" && tc !== null && typeof tc.type === "string" && tc.type === "auto") {
      return JSON.stringify("auto");
    }
    if (typeof tc === "object" && tc !== null && typeof tc.type === "string" && tc.type === "required") {
      return JSON.stringify("required");
    }
    if (typeof tc === "object" && tc !== null && typeof tc.type === "string" && tc.type === "function") {
      const tcFunction = tc.function;
      if (typeof tcFunction === "object" && tcFunction !== null && typeof tcFunction.name === "string" && tcFunction.name.length > 0) {
        return JSON.stringify({ type: "function", function: { name: tcFunction.name } });
      }
    }
    return null;
  } catch (e) {
    return null;
  }
}

// Convert tools
export function convertTools(toolsJson) {
  if (!toolsJson) return null;
  try {
    const tools = typeof toolsJson === "string" ? JSON.parse(toolsJson) : toolsJson;
    if (!Array.isArray(tools)) return null;
    const converted = tools.map((tool) => {
      if (tool.type === "function") {
        return {
          type: "function",
          name: typeof tool.function === "object" && tool.function !== null ? tool.function.name : null,
          description: typeof tool.function === "object" && tool.function !== null ? tool.function.description : null,
          parameters: typeof tool.function === "object" && tool.function !== null ? tool.function.parameters : null,
          strict: typeof tool.function === "object" && tool.function !== null ? tool.function.strict : null,
        };
      }
      return tool;
    });
    return JSON.stringify(converted);
  } catch (e) {
    return null;
  }
}

// Parse JSON (identity for FFI - already parsed)
export function parseJson(jsonStr) {
  return jsonStr; // Already a JSON string representation
}

// Stringify JSON (identity for FFI - already stringified)
export function stringifyJson(obj) {
  return obj; // Already a JSON string
}

// Get field from JSON object
export function getField(objJson, key, defaultValue) {
  try {
    const obj = typeof objJson === "string" ? JSON.parse(objJson) : objJson;
    const value = obj[key];
    if (value === null || (typeof value === "undefined")) {
      return typeof defaultValue === "string" ? defaultValue : JSON.stringify(defaultValue);
    }
    return typeof value === "string" ? value : JSON.stringify(value);
  } catch (e) {
    return typeof defaultValue === "string" ? defaultValue : JSON.stringify(defaultValue);
  }
}

// Get field maybe
export function getFieldMaybe(objJson, key) {
  try {
    const obj = typeof objJson === "string" ? JSON.parse(objJson) : objJson;
    const value = obj[key];
    if (value === null || typeof value === "undefined") {
      return null;
    }
    return JSON.stringify(value);
  } catch (e) {
    return null;
  }
}

// Full fromOpenaiRequest implementation
export function fromOpenaiRequestImpl(bodyJson) {
  try {
    const body = typeof bodyJson === "string" ? JSON.parse(bodyJson) : bodyJson;
    if (!body || typeof body !== "object") {
      return { model: "", messages: [], stream: false };
    }

    const msgs = [];
    const inMsgs = Array.isArray(body.input) ? body.input : Array.isArray(body.messages) ? body.messages : [];

    for (const m of inMsgs) {
      if (!m) continue;

      // Responses API items without role
      if (!m.role && m.type) {
        if (m.type === "function_call") {
          const name = m.name;
          const a = m.arguments;
          const args = typeof a === "string" ? a : (a !== null && typeof a !== "undefined" ? JSON.stringify(a) : JSON.stringify({}));
          msgs.push({
            role: "assistant",
            tool_calls: [{ id: m.id, type: "function", function: { name, arguments: args } }],
          });
        }
        if (m.type === "function_call_output") {
          const id = m.call_id;
          const out = m.output;
          const content = typeof out === "string" ? out : JSON.stringify(out);
          msgs.push({ role: "tool", tool_call_id: id, content });
        }
        continue;
      }

      if (m.role === "system" || m.role === "developer") {
        const c = m.content;
        if (typeof c === "string" && c.length > 0) {
          msgs.push({ role: "system", content: c });
        }
        if (Array.isArray(c)) {
          const t = c.find((p) => p && typeof p.text === "string");
          if (t && typeof t.text === "string" && t.text.length > 0) {
            msgs.push({ role: "system", content: t.text });
          }
        }
        continue;
      }

      if (m.role === "user") {
        const c = m.content;
        if (typeof c === "string") {
          msgs.push({ role: "user", content: c });
        } else if (Array.isArray(c)) {
          const parts = [];
          for (const p of c) {
            if (!p || !p.type) continue;
            if ((p.type === "text" || p.type === "input_text") && typeof p.text === "string") {
              parts.push({ type: "text", text: p.text });
            }
            const ip = toImg(p);
            if (ip) parts.push(ip);
            if (p.type === "tool_result") {
              const id = p.tool_call_id;
              const content = typeof p.content === "string" ? p.content : JSON.stringify(p.content);
              msgs.push({ role: "tool", tool_call_id: id, content });
            }
          }
          if (parts.length === 1 && parts[0].type === "text") {
            msgs.push({ role: "user", content: parts[0].text });
          } else if (parts.length > 0) {
            msgs.push({ role: "user", content: parts });
          }
        }
        continue;
      }

      if (m.role === "assistant") {
        const c = m.content;
        const out = { role: "assistant" };
        if (typeof c === "string" && c.length > 0) out.content = c;
        if (Array.isArray(m.tool_calls)) out.tool_calls = m.tool_calls;
        msgs.push(out);
        continue;
      }

      if (m.role === "tool") {
        msgs.push({
          role: "tool",
          tool_call_id: m.tool_call_id,
          content: m.content,
        });
        continue;
      }
    }

    const tcIn = body.tool_choice;
    const tc = (() => {
      if (!tcIn) return null;
      if (tcIn === "auto") return "auto";
      if (tcIn === "required") return "required";
      if (tcIn.type === "function" && tcIn.function !== null && typeof tcIn.function !== "undefined" && typeof tcIn.function.name === "string") {
        return { type: "function", function: { name: tcIn.function.name } };
      }
      return null;
    })();

    const stop = (() => {
      const v = body.stop_sequences !== null && typeof body.stop_sequences !== "undefined" ? body.stop_sequences : body.stop;
      if (!v) return null;
      if (Array.isArray(v)) return v.length === 1 ? v[0] : v;
      if (typeof v === "string") return v;
      return null;
    })();

    const modelValue = typeof body.model === "string" && body.model.length > 0 ? body.model : "";
    const maxTokensValue = body.max_output_tokens !== null && typeof body.max_output_tokens !== "undefined" ? body.max_output_tokens : body.max_tokens;
    const stopValue = stop !== null ? (Array.isArray(stop) ? stop : [stop]) : null;
    const toolsValue = Array.isArray(body.tools) ? body.tools : null;

    return {
      model: modelValue,
      maxTokens: maxTokensValue,
      temperature: body.temperature,
      topP: body.top_p,
      stop: stopValue,
      messages: msgs,
      stream: !!body.stream,
      tools: toolsValue,
      toolChoice: tc,
    };
  } catch (e) {
    return { model: "", messages: [], stream: false };
  }
}

// Full toOpenaiRequest implementation
export function toOpenaiRequestImpl(req) {
  try {
    if (!req || typeof req !== "object") {
      return JSON.stringify({ model: "", input: [] });
    }

    const msgsIn = Array.isArray(req.messages) ? req.messages : [];
    const input = [];

    for (const m of msgsIn) {
      if (!m || !m.role) continue;

      if (m.role === "system") {
        const c = m.content;
        if (typeof c === "string") {
          input.push({ role: "system", content: c });
        }
        continue;
      }

      if (m.role === "user") {
        const c = m.content;
        if (typeof c === "string") {
          input.push({ role: "user", content: [{ type: "input_text", text: c }] });
        } else if (Array.isArray(c)) {
          const parts = [];
          for (const p of c) {
            const op = toPart(p);
            if (op) parts.push(op);
          }
          if (parts.length > 0) {
            input.push({ role: "user", content: parts });
          }
        }
        continue;
      }

      if (m.role === "assistant") {
        const c = m.content;
        if (typeof c === "string" && c.length > 0) {
          input.push({ role: "assistant", content: [{ type: "output_text", text: c }] });
        }
        if (Array.isArray(m.tool_calls)) {
          for (const tc of m.tool_calls) {
            if (tc.type === "function" && tc.function) {
              const name = tc.function.name;
              const a = tc.function.arguments;
              const args = typeof a === "string" ? a : JSON.stringify(a);
              input.push({ type: "function_call", call_id: tc.id, name, arguments: args });
            }
          }
        }
        continue;
      }

      if (m.role === "tool") {
        const out = typeof m.content === "string" ? m.content : JSON.stringify(m.content);
        input.push({ type: "function_call_output", call_id: m.tool_call_id, output: out });
        continue;
      }
    }

    const stop_sequences = (() => {
      const v = req.stop;
      if (!v) return null;
      if (Array.isArray(v)) return v;
      if (typeof v === "string") return [v];
      return null;
    })();

    const tcIn = req.toolChoice;
    const tool_choice = (() => {
      if (!tcIn) return null;
      if (tcIn === "auto") return "auto";
      if (tcIn === "required") return "required";
      if (tcIn.type === "function" && tcIn.function !== null && typeof tcIn.function !== "undefined" && typeof tcIn.function.name === "string") {
        return { type: "function", function: { name: tcIn.function.name } };
      }
      return null;
    })();

    const tools = (() => {
      if (!Array.isArray(req.tools)) return null;
      return req.tools.map((tool) => {
        if (tool.type === "function") {
          return {
            type: "function",
          name: typeof tool.function === "object" && tool.function !== null ? tool.function.name : null,
          description: typeof tool.function === "object" && tool.function !== null ? tool.function.description : null,
          parameters: typeof tool.function === "object" && tool.function !== null ? tool.function.parameters : null,
          strict: typeof tool.function === "object" && tool.function !== null ? tool.function.strict : null,
        };
        }
        return tool;
      });
    })();

    return JSON.stringify({
      model: typeof req.model === "string" && req.model.length > 0 ? req.model : "",
      input,
      max_output_tokens: req.maxTokens,
      top_p: req.topP,
      stop_sequences,
      stream: !!req.stream,
      tools,
      tool_choice,
      text: { verbosity: req.model === "gpt-5-codex" ? "medium" : "low" },
      reasoning: { effort: "medium" },
    });
  } catch (e) {
    return JSON.stringify({ model: "", input: [] });
  }
}
