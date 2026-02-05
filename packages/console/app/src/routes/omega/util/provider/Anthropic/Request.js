// Anthropic Request Conversion FFI
// Full implementation
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/anthropic.ts
// Migrated: 2026-02-04

export function fromAnthropicRequestImpl(bodyJson) {
  try {
    const body = typeof bodyJson === "string" ? JSON.parse(bodyJson) : bodyJson;
    if (!body || typeof body !== "object") {
      return { model: "", messages: [], stream: false };
    }

    const msgs = [];

    const sys = Array.isArray(body.system) ? body.system : null;
    if (Array.isArray(sys) && sys.length > 0) {
      for (const s of sys) {
        if (!s) continue;
        if (s.type !== "text") continue;
        if (typeof s.text !== "string") continue;
        if (s.text.length === 0) continue;
        msgs.push({ role: "system", content: s.text });
      }
    }

    const toImg = (src) => {
      if (!src || typeof src !== "object") return null;
      if (src.type === "url" && typeof src.url === "string") {
        return { type: "image_url", image_url: { url: src.url } };
      }
      if (src.type === "base64" && typeof src.media_type === "string" && typeof src.data === "string") {
        return {
          type: "image_url",
          image_url: { url: `data:${src.media_type};base64,${src.data}` },
        };
      }
      return null;
    };

    const inMsgs = Array.isArray(body.messages) ? body.messages : [];
    for (const m of inMsgs) {
      if (!m || !m.role) continue;

      if (m.role === "user") {
        const partsIn = Array.isArray(m.content) ? m.content : [];
        const partsOut = [];
        for (const p of partsIn) {
          if (!p || !p.type) continue;
          if (p.type === "text" && typeof p.text === "string") {
            partsOut.push({ type: "text", text: p.text });
          }
          if (p.type === "image") {
            const ip = toImg(p.source);
            if (ip) partsOut.push(ip);
          }
          if (p.type === "tool_result") {
            const id = p.tool_use_id;
            const content = typeof p.content === "string" ? p.content : JSON.stringify(p.content);
            msgs.push({ role: "tool", tool_call_id: id, content });
          }
        }
        if (partsOut.length > 0) {
          if (partsOut.length === 1 && partsOut[0].type === "text") {
            msgs.push({ role: "user", content: partsOut[0].text });
          } else {
            msgs.push({ role: "user", content: partsOut });
          }
        }
        continue;
      }

      if (m.role === "assistant") {
        const partsIn = Array.isArray(m.content) ? m.content : [];
        const texts = [];
        const tcs = [];
        for (const p of partsIn) {
          if (!p || !p.type) continue;
          if (p.type === "text" && typeof p.text === "string") {
            texts.push(p.text);
          }
          if (p.type === "tool_use") {
            const name = p.name;
            const id = p.id;
            const inp = p.input;
            const input = (() => {
              if (typeof inp === "string") return inp;
              try {
                return typeof inp === "object" && inp !== null ? JSON.stringify(inp) : JSON.stringify({});
              } catch {
                return typeof inp === "string" ? String(inp) : String("");
              }
            })();
            tcs.push({ id, type: "function", function: { name, arguments: input } });
          }
        }
        const out = { role: "assistant", content: texts.join("") };
        if (tcs.length > 0) out.tool_calls = tcs;
        msgs.push(out);
        continue;
      }
    }

    const tools = Array.isArray(body.tools)
      ? body.tools
          .filter((t) => t && typeof t === "object" && "input_schema" in t)
          .map((t) => ({
            type: "function",
            function: {
              name: t.name,
              description: t.description,
              parameters: t.input_schema,
            },
          }))
      : null;

    const tcin = body.tool_choice;
    const tc = (() => {
      if (!tcin) return null;
      if (tcin.type === "auto") return "auto";
      if (tcin.type === "any") return "required";
      if (tcin.type === "tool" && typeof tcin.name === "string") {
        return { type: "function", function: { name: tcin.name } };
      }
      return null;
    })();

    const stop = (() => {
      const v = body.stop_sequences;
      if (!v) return null;
      if (Array.isArray(v)) return v.length === 1 ? v[0] : v;
      if (typeof v === "string") return v;
      return null;
    })();

    return {
      model: body.model || "",
      maxTokens: body.max_tokens,
      temperature: body.temperature,
      topP: body.top_p,
      stop: stop !== null ? (Array.isArray(stop) ? stop : [stop]) : null,
      messages: msgs,
      stream: !!body.stream,
      tools,
      toolChoice: tc,
    };
  } catch (e) {
    return { model: "", messages: [], stream: false };
  }
}

export function toAnthropicRequestImpl(req) {
  try {
    if (!req || typeof req !== "object") {
      return JSON.stringify({ model: "", messages: [] });
    }

    const msgsOut = [];
    const sys = [];

    const messagesArray = Array.isArray(req.messages) ? req.messages : [];
    for (const m of messagesArray) {
      if (!m || !m.role) continue;

      if (m.role === "system") {
        const c = m.content;
        if (typeof c === "string" && c.length > 0) {
          sys.push({ type: "text", text: c });
        }
        continue;
      }

      if (m.role === "user") {
        const c = m.content;
        const parts = [];
        if (typeof c === "string") {
          parts.push({ type: "text", text: c });
        } else if (Array.isArray(c)) {
          for (const p of c) {
            if (!p || !p.type) continue;
            if (p.type === "text" && typeof p.text === "string") {
              parts.push({ type: "text", text: p.text });
            }
            if (p.type === "image_url" && p.image_url) {
              const url = typeof p.image_url === "string" ? p.image_url : p.image_url.url;
              if (url.startsWith("data:")) {
                const [header, data] = url.split(",");
                const [mediaType] = header.split(";");
                parts.push({
                  type: "image",
                  source: {
                    type: "base64",
                    media_type: mediaType.replace("data:", ""),
                    data: data,
                  },
                });
              } else {
                parts.push({ type: "image", source: { type: "url", url } });
              }
            }
          }
        }
        if (parts.length > 0) {
          msgsOut.push({ role: "user", content: parts });
        }
        continue;
      }

      if (m.role === "assistant") {
        const parts = [];
        const c = m.content;
        if (typeof c === "string" && c.length > 0) {
          parts.push({ type: "text", text: c });
        }
        if (Array.isArray(m.tool_calls)) {
          for (const tc of m.tool_calls) {
            if (tc.type === "function" && tc.function) {
              let input;
              try {
                input = JSON.parse(tc.function.arguments);
              } catch {
                input = tc.function.arguments;
              }
              parts.push({
                type: "tool_use",
                id: tc.id,
                name: tc.function.name,
                input,
              });
            }
          }
        }
        if (parts.length > 0) {
          msgsOut.push({ role: "assistant", content: parts });
        }
        continue;
      }

      if (m.role === "tool") {
        const content = typeof m.content === "string" ? m.content : JSON.stringify(m.content);
        msgsOut.push({
          role: "user",
          content: [{ type: "tool_result", tool_use_id: m.tool_call_id, content }],
        });
        continue;
      }
    }

    const tools = Array.isArray(req.tools)
      ? req.tools.map((tool) => ({
          name: typeof tool.function === "object" && tool.function !== null ? tool.function.name : null,
          description: typeof tool.function === "object" && tool.function !== null ? tool.function.description : null,
          input_schema: typeof tool.function === "object" && tool.function !== null ? tool.function.parameters : null,
        }))
      : null;

    const tcin = req.toolChoice;
    const tc = (() => {
      if (!tcin) return null;
      if (tcin === "auto") return { type: "auto" };
      if (tcin === "required") return { type: "any" };
      if (typeof tcin === "object" && tcin !== null && typeof tcin.type === "string" && tcin.type === "function") {
        const tcinFunction = tcin.function;
        if (typeof tcinFunction === "object" && tcinFunction !== null && typeof tcinFunction.name === "string" && tcinFunction.name.length > 0) {
        return { type: "tool", name: tcin.function.name };
      }
      return null;
    })();

    const stop = (() => {
      const v = req.stop;
      if (!v) return null;
      if (Array.isArray(v)) return v;
      if (typeof v === "string") return [v];
      return null;
    })();

    return JSON.stringify({
      model: typeof req.model === "string" && req.model.length > 0 ? req.model : "",
      ...(sys.length > 0 ? { system: sys } : {}),
      messages: msgsOut,
      max_tokens: req.maxTokens,
      temperature: req.temperature,
      top_p: req.topP,
      stop_sequences: stop,
      stream: !!req.stream,
      tools,
      tool_choice: tc,
    });
  } catch (e) {
    return JSON.stringify({ model: "", messages: [] });
  }
}
