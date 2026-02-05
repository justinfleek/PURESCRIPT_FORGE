// OpenAI Response Conversion FFI
// Full implementation of fromOpenaiResponse and toOpenaiResponse
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/openai.ts
// Migrated: 2026-02-04

// Full fromOpenaiResponse implementation
export function fromOpenaiResponseImpl(respJson) {
  try {
    const resp = typeof respJson === "string" ? JSON.parse(respJson) : respJson;
    if (!resp || typeof resp !== "object") {
      return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
    }
    
    // Already in CommonResponse format (has choices array)
    if (Array.isArray(resp.choices)) {
      return resp;
    }

    const r = resp.response !== null && typeof resp.response !== "undefined" ? resp.response : resp;
    if (!r || typeof r !== "object") {
      return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
    }

    const idIn = r.id;
    const id = typeof idIn === "string" ? idIn.replace(/^resp_/, "chatcmpl_") : `chatcmpl_${Math.random().toString(36).slice(2)}`;
    const modelValue = r.model !== null && typeof r.model !== "undefined" ? r.model : (resp.model !== null && typeof resp.model !== "undefined" ? resp.model : "");

    const out = Array.isArray(r.output) ? r.output : [];
    const text = out
      .filter((o) => o && o.type === "message" && Array.isArray(o.content))
      .flatMap((o) => o.content)
      .filter((p) => typeof p === "object" && p !== null && typeof p.type === "string" && p.type === "output_text" && typeof p.text === "string")
      .map((p) => p.text)
      .join("");

    const tcs = out
      .filter((o) => o && o.type === "function_call")
      .map((o) => {
        const name = o.name;
        const a = o.arguments;
        const args = typeof a === "string" ? a : (a !== null && typeof a !== "undefined" ? JSON.stringify(a) : JSON.stringify({}));
        const tid = typeof o.id === "string" && o.id.length > 0 ? o.id : `toolu_${Math.random().toString(36).slice(2)}`;
        return { id: tid, type: "function", function: { name, arguments: args } };
      });

    const finish = (r) => {
      if (r === "stop") return "stop";
      if (r === "tool_call" || r === "tool_calls") return "tool_calls";
      if (r === "length" || r === "max_output_tokens") return "length";
      if (r === "content_filter") return "content_filter";
      return null;
    };

    const rUsage = r.usage;
    const respUsage = resp.usage;
    const u = typeof rUsage === "object" && rUsage !== null ? rUsage : respUsage;
    const usage = (() => {
      if (!u) return null;
      const pt = typeof u.input_tokens === "number" ? u.input_tokens : null;
      const ct = typeof u.output_tokens === "number" ? u.output_tokens : null;
      const total = pt !== null && ct !== null ? pt + ct : null;
      const inputDetails = u.input_tokens_details;
      const cached = inputDetails !== null && typeof inputDetails === "object" && typeof inputDetails.cached_tokens === "number" ? inputDetails.cached_tokens : null;
      const details = cached !== null ? { cached_tokens: cached } : null;
      const result = {};
      if (pt !== null) result.prompt_tokens = pt;
      if (ct !== null) result.completion_tokens = ct;
      if (total !== null) result.total_tokens = total;
      if (details !== null) result.prompt_tokens_details = details;
      return Object.keys(result).length > 0 ? result : null;
    })();

    return {
      id,
      object: "chat.completion",
      created: Math.floor(Date.now() / 1000),
      model,
      choices: [
        {
          index: 0,
          message: {
            role: "assistant",
            ...(typeof text === "string" && text.length > 0 ? { content: text } : {}),
            ...(tcs.length > 0 ? { tool_calls: tcs } : {}),
          },
          finish_reason: finish(r.stop_reason !== null && typeof r.stop_reason !== "undefined" ? r.stop_reason : null),
        },
      ],
      ...(usage ? { usage } : {}),
    };
  } catch (e) {
    return { id: "", object: "chat.completion", created: Math.floor(Date.now() / 1000), model: "", choices: [] };
  }
}

// Full toOpenaiResponse implementation
export function toOpenaiResponseImpl(resp) {
  try {
    if (!resp || typeof resp !== "object") {
      return JSON.stringify({ id: "", object: "response", model: "", output: [] });
    }
    if (!Array.isArray(resp.choices)) {
      return JSON.stringify(resp);
    }

    const choice = resp.choices[0];
    if (!choice) {
      return JSON.stringify(resp);
    }

    const msg = choice.message;
    if (!msg) {
      return JSON.stringify(resp);
    }

    const outputItems = [];

    if (typeof msg.content === "string" && msg.content.length > 0) {
      outputItems.push({
        id: `msg_${Math.random().toString(36).slice(2)}`,
        type: "message",
        status: "completed",
        role: "assistant",
        content: [{ type: "output_text", text: msg.content, annotations: [], logprobs: [] }],
      });
    }

    if (Array.isArray(msg.tool_calls)) {
      for (const tc of msg.tool_calls) {
        if (tc.type === "function" && tc.function) {
          outputItems.push({
            id: tc.id,
            type: "function_call",
            name: tc.function.name,
            call_id: tc.id,
            arguments: tc.function.arguments,
          });
        }
      }
    }

    const stop_reason = (() => {
      const r = choice.finish_reason;
      if (r === "stop") return "stop";
      if (r === "tool_calls") return "tool_call";
      if (r === "length") return "max_output_tokens";
      if (r === "content_filter") return "content_filter";
      return null;
    })();

    const usage = (() => {
      const u = resp.usage;
      if (!u) return null;
      const promptDetails = u.prompt_tokens_details;
      const cachedTokens = promptDetails !== null && typeof promptDetails !== "undefined" && typeof promptDetails === "object" && typeof promptDetails.cached_tokens === "number" ? promptDetails.cached_tokens : null;
      const result = {
        input_tokens: u.prompt_tokens,
        output_tokens: u.completion_tokens,
        total_tokens: u.total_tokens,
      };
      if (cachedTokens !== null) {
        result.input_tokens_details = { cached_tokens: cachedTokens };
      }
      return result;
    })();

    const respId = resp.id;
    const idValue = typeof respId === "string" && respId.length > 0 ? respId.replace(/^chatcmpl_/, "resp_") : `resp_${Math.random().toString(36).slice(2)}`;
    const result = {
      id: idValue,
      object: "response",
      model: resp.model,
      output: outputItems,
      stop_reason,
    };
    if (usage !== null) result.usage = usage;
    return JSON.stringify(result);
  } catch (e) {
    return JSON.stringify({ id: "", object: "response", model: "", output: [] });
  }
}
