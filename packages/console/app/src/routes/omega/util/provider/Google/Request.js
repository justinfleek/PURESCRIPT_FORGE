// Google Request Conversion FFI
export function fromGoogleRequestImpl(bodyJson) {
  try {
    const body = typeof bodyJson === "string" ? JSON.parse(bodyJson) : bodyJson;
    if (!body || typeof body !== "object") {
      return { model: "", messages: [], stream: false };
    }

    const contents = Array.isArray(body.contents) ? body.contents : [];
    const msgs = [];

    for (const c of contents) {
      if (!c || !c.role) continue;

      if (c.role === "user") {
        const parts = Array.isArray(c.parts) ? c.parts : [];
        const contentParts = [];
        for (const p of parts) {
          if (p.text) {
            contentParts.push({ type: "text", text: p.text });
          }
          if (p.inlineData) {
            contentParts.push({
              type: "image_url",
              image_url: { url: `data:${p.inlineData.mimeType};base64,${p.inlineData.data}` },
            });
          }
        }
        if (contentParts.length === 1 && contentParts[0].type === "text") {
          msgs.push({ role: "user", content: contentParts[0].text });
        } else if (contentParts.length > 0) {
          msgs.push({ role: "user", content: contentParts });
        }
      } else if (c.role === "model") {
        const parts = Array.isArray(c.parts) ? c.parts : [];
        const text = parts.filter((p) => p.text).map((p) => p.text).join("");
        if (text) {
          msgs.push({ role: "assistant", content: text });
        }
      }
    }

    return {
      model: typeof body.model === "string" && body.model.length > 0 ? body.model : "",
      maxTokens: body.maxOutputTokens,
      temperature: body.temperature,
      topP: body.topP,
      stop: body.stopSequences,
      messages: msgs,
      stream: !!body.stream,
      tools: null,
      toolChoice: null,
    };
  } catch (e) {
    return { model: "", messages: [], stream: false };
  }
}

export function toGoogleRequestImpl(req) {
  try {
    if (!req || typeof req !== "object") {
      return JSON.stringify({ model: "", contents: [] });
    }

    const contents = [];
    const messagesArray = Array.isArray(req.messages) ? req.messages : [];
    for (const m of messagesArray) {
      if (!m || !m.role) continue;

      if (m.role === "user") {
        const parts = [];
        if (typeof m.content === "string") {
          parts.push({ text: m.content });
        } else if (Array.isArray(m.content)) {
          for (const p of m.content) {
            if (p.type === "text") {
              parts.push({ text: p.text });
            } else if (p.type === "image_url") {
              const url = typeof p.image_url === "string" ? p.image_url : p.image_url.url;
              if (url.startsWith("data:")) {
                const [header, data] = url.split(",");
                const [mimeType] = header.split(";");
                parts.push({
                  inlineData: {
                    mimeType: mimeType.replace("data:", ""),
                    data: data,
                  },
                });
              }
            }
          }
        }
        if (parts.length > 0) {
          contents.push({ role: "user", parts });
        }
      } else if (m.role === "assistant") {
        if (typeof m.content === "string" && m.content.length > 0) {
          contents.push({ role: "model", parts: [{ text: m.content }] });
        }
      }
    }

    return JSON.stringify({
      model: typeof req.model === "string" && req.model.length > 0 ? req.model : "",
      contents,
      maxOutputTokens: req.maxTokens,
      temperature: req.temperature,
      topP: req.topP,
      stopSequences: req.stop,
      stream: !!req.stream,
    });
  } catch (e) {
    return JSON.stringify({ model: "", contents: [] });
  }
}
