// OpenAI-Compatible Request Conversion FFI
export function fromOaCompatibleRequestImpl(bodyJson) {
  try {
    const body = typeof bodyJson === "string" ? JSON.parse(bodyJson) : bodyJson;
    if (!body || typeof body !== "object") {
      return { model: "", messages: [], stream: false };
    }

    const msgsOut = [];
    const msgsIn = Array.isArray(body.messages) ? body.messages : [];

    for (const m of msgsIn) {
      if (!m || !m.role) continue;

      if (m.role === "system") {
        if (typeof m.content === "string" && m.content.length > 0) {
          msgsOut.push({ role: "system", content: m.content });
        }
        continue;
      }

      if (m.role === "user") {
        if (typeof m.content === "string") {
          msgsOut.push({ role: "user", content: m.content });
        } else if (Array.isArray(m.content)) {
          const parts = [];
          for (const p of m.content) {
            if (!p || !p.type) continue;
            if (p.type === "text" && typeof p.text === "string") {
              parts.push({ type: "text", text: p.text });
            }
            if (p.type === "image_url") {
              parts.push({ type: "image_url", image_url: p.image_url });
            }
          }
          if (parts.length === 1 && parts[0].type === "text") {
            msgsOut.push({ role: "user", content: parts[0].text });
          } else if (parts.length > 0) {
            msgsOut.push({ role: "user", content: parts });
          }
        }
        continue;
      }

      if (m.role === "assistant") {
        const out = { role: "assistant" };
        if (typeof m.content === "string") out.content = m.content;
        if (Array.isArray(m.tool_calls)) out.tool_calls = m.tool_calls;
        msgsOut.push(out);
        continue;
      }

      if (m.role === "tool") {
        msgsOut.push({ role: "tool", tool_call_id: m.tool_call_id, content: m.content });
        continue;
      }
    }

    return {
      model: body.model || "",
      maxTokens: body.max_tokens,
      temperature: body.temperature,
      topP: body.top_p,
      stop: body.stop,
      messages: msgsOut,
      stream: !!body.stream,
      tools: Array.isArray(body.tools) ? body.tools : undefined,
      toolChoice: body.tool_choice,
    };
  } catch (e) {
    return { model: "", messages: [], stream: false };
  }
}

export function toOaCompatibleRequestImpl(req) {
  try {
    if (!req || typeof req !== "object") {
      return JSON.stringify({ model: "", messages: [] });
    }

    const msgsOut = [];
    const msgsIn = Array.isArray(req.messages) ? req.messages : [];

    const toImg = (p) => {
      if (!p || typeof p !== "object") return undefined;
      if (p.type === "image_url" && p.image_url) {
        return { type: "image_url", image_url: p.image_url };
      }
      return undefined;
    };

    for (const m of msgsIn) {
      if (!m || !m.role) continue;

      if (m.role === "system") {
        if (typeof m.content === "string" && m.content.length > 0) {
          msgsOut.push({ role: "system", content: m.content });
        }
        continue;
      }

      if (m.role === "user") {
        if (typeof m.content === "string") {
          msgsOut.push({ role: "user", content: m.content });
        } else if (Array.isArray(m.content)) {
          const parts = [];
          for (const p of m.content) {
            if (!p || !p.type) continue;
            if (p.type === "text" && typeof p.text === "string") {
              parts.push({ type: "text", text: p.text });
            }
            const ip = toImg(p);
            if (ip) parts.push(ip);
          }
          if (parts.length === 1 && parts[0].type === "text") {
            msgsOut.push({ role: "user", content: parts[0].text });
          } else if (parts.length > 0) {
            msgsOut.push({ role: "user", content: parts });
          }
        }
        continue;
      }

      if (m.role === "assistant") {
        const out = { role: "assistant" };
        if (typeof m.content === "string") out.content = m.content;
        if (Array.isArray(m.tool_calls)) out.tool_calls = m.tool_calls;
        msgsOut.push(out);
        continue;
      }

      if (m.role === "tool") {
        msgsOut.push({ role: "tool", tool_call_id: m.tool_call_id, content: m.content });
        continue;
      }
    }

    const tools = Array.isArray(req.tools)
      ? req.tools.map((tool) => ({
          type: "function",
          function: {
            name: tool.function?.name,
            description: tool.function?.description,
            parameters: tool.function?.parameters,
          },
        }))
      : undefined;

    return JSON.stringify({
      model: req.model || "",
      max_tokens: req.maxTokens,
      temperature: req.temperature,
      top_p: req.topP,
      stop: req.stop,
      messages: msgsOut,
      stream: !!req.stream,
      tools,
      tool_choice: req.toolChoice,
    });
  } catch (e) {
    return JSON.stringify({ model: "", messages: [] });
  }
}
