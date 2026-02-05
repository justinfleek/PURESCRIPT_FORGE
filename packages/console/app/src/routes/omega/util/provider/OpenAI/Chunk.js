// OpenAI Chunk Conversion FFI
// Full implementation of fromOpenaiChunk and toOpenaiChunk
// FULL DETERMINISM - NO ??, ?., lazy &&, undefined, null without explicit handling
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/openai.ts
// Migrated: 2026-02-04

// Full fromOpenaiChunk implementation
export function fromOpenaiChunkImpl(chunkStr) {
  try {
    const lines = chunkStr.split("\n");
    const ev = lines[0];
    const dl = lines[1];
    if (typeof ev !== "string" || typeof dl !== "string" || dl.length < 6 || dl.substring(0, 6) !== "data: ") {
      return { error: chunkStr };
    }

    let json;
    try {
      json = JSON.parse(dl.slice(6));
    } catch (e) {
      return { error: chunkStr };
    }

    const jsonResponse = json.response;
    const respObj = typeof jsonResponse === "object" && jsonResponse !== null ? jsonResponse : {};

    const respObjId = respObj.id;
    const jsonId = json.id;
    const idValue = typeof respObjId === "string" && respObjId.length > 0 ? respObjId : (typeof jsonId === "string" && jsonId.length > 0 ? jsonId : "");

    const respObjModel = respObj.model;
    const jsonModel = json.model;
    const modelValue = typeof respObjModel === "string" && respObjModel.length > 0 ? respObjModel : (typeof jsonModel === "string" && jsonModel.length > 0 ? jsonModel : "");

    const out = {
      id: idValue,
      object: "chat.completion.chunk",
      created: Math.floor(Date.now() / 1000),
      model: modelValue,
      choices: [],
    };

    const e = ev.replace("event: ", "").trim();

    if (e === "response.output_text.delta") {
      const jsonDelta = json.delta;
      const jsonText = json.text;
      const jsonOutputTextDelta = json.output_text_delta;
      const d = typeof jsonDelta === "string" && jsonDelta.length > 0 ? jsonDelta : (typeof jsonText === "string" && jsonText.length > 0 ? jsonText : (typeof jsonOutputTextDelta === "string" && jsonOutputTextDelta.length > 0 ? jsonOutputTextDelta : ""));
      if (typeof d === "string" && d.length > 0) {
        out.choices.push({ index: 0, delta: { content: d }, finish_reason: null });
      }
    }

    if (e === "response.output_item.added") {
      const jsonItem = json.item;
      if (typeof jsonItem === "object" && jsonItem !== null && typeof jsonItem.type === "string" && jsonItem.type === "function_call") {
        const itemName = jsonItem.name;
        const itemId = jsonItem.id;
        if (typeof itemName === "string" && itemName.length > 0) {
          out.choices.push({
            index: 0,
            delta: {
              tool_calls: [{ index: 0, id: itemId, type: "function", function: { name: itemName, arguments: "" } }],
            },
            finish_reason: null,
          });
        }
      }
    }

    if (e === "response.function_call_arguments.delta") {
      const jsonDelta = json.delta;
      const jsonArgumentsDelta = json.arguments_delta;
      const a = typeof jsonDelta === "string" && jsonDelta.length > 0 ? jsonDelta : (typeof jsonArgumentsDelta === "string" && jsonArgumentsDelta.length > 0 ? jsonArgumentsDelta : "");
      if (typeof a === "string" && a.length > 0) {
        out.choices.push({
          index: 0,
          delta: { tool_calls: [{ index: 0, function: { arguments: a } }] },
          finish_reason: null,
        });
      }
    }

    if (e === "response.completed") {
      const respObjStopReason = respObj.stop_reason;
      const jsonStopReason = json.stop_reason;
      const sr = typeof respObjStopReason === "string" && respObjStopReason.length > 0 ? respObjStopReason : (typeof jsonStopReason === "string" && jsonStopReason.length > 0 ? jsonStopReason : "");
      const fr = (() => {
        if (sr === "stop") return "stop";
        if (sr === "tool_call" || sr === "tool_calls") return "tool_calls";
        if (sr === "length" || sr === "max_output_tokens") return "length";
        if (sr === "content_filter") return "content_filter";
        return null;
      })();
      out.choices.push({ index: 0, delta: {}, finish_reason: fr });

      const respObjUsage = respObj.usage;
      const jsonResponseObj = json.response;
      const jsonResponseUsage = typeof jsonResponseObj === "object" && jsonResponseObj !== null ? jsonResponseObj.usage : null;
      const u = typeof respObjUsage === "object" && respObjUsage !== null ? respObjUsage : jsonResponseUsage;
      if (typeof u === "object" && u !== null) {
        const uInputTokens = u.input_tokens;
        const uOutputTokens = u.output_tokens;
        const inputTokensValue = typeof uInputTokens === "number" ? uInputTokens : 0;
        const outputTokensValue = typeof uOutputTokens === "number" ? uOutputTokens : 0;
        const totalTokensValue = inputTokensValue + outputTokensValue;

        const uInputTokensDetails = u.input_tokens_details;
        const cachedTokens = typeof uInputTokensDetails === "object" && uInputTokensDetails !== null && typeof uInputTokensDetails.cached_tokens === "number" ? uInputTokensDetails.cached_tokens : null;

        const usageResult = {
          prompt_tokens: inputTokensValue,
          completion_tokens: outputTokensValue,
          total_tokens: totalTokensValue,
        };
        if (cachedTokens !== null) {
          usageResult.prompt_tokens_details = { cached_tokens: cachedTokens };
        }
        out.usage = usageResult;
      }
    }

    return out;
  } catch (e) {
    return { error: chunkStr };
  }
}

// Full toOpenaiChunk implementation
export function toOpenaiChunkImpl(chunk) {
  try {
    if (typeof chunk !== "object" || chunk === null || !Array.isArray(chunk.choices) || chunk.choices.length === 0) {
      return "";
    }

    const choice = chunk.choices[0];
    const d = choice.delta;
    if (typeof d !== "object" || d === null) return "";

    const id = chunk.id;
    const model = chunk.model;

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
  } catch (e) {
    return "";
  }
}
