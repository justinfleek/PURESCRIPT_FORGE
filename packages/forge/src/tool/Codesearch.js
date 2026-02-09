// FFI for Forge.Tool.Codesearch
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/codesearch.ts

const API_CONFIG = {
  BASE_URL: "https://mcp.exa.ai",
  ENDPOINTS: {
    CONTEXT: "/mcp",
  },
};

export const execute = (params) => (ctx) => async () => {
  await ctx.ask({
    permission: "codesearch",
    patterns: [params.query],
    always: ["*"],
    metadata: {
      query: params.query,
      tokensNum: params.tokensNum,
    },
  })();

  const codeRequest = {
    jsonrpc: "2.0",
    id: 1,
    method: "tools/call",
    params: {
      name: "get_code_context_exa",
      arguments: {
        query: params.query,
        tokensNum: params.tokensNum || 5000,
      },
    },
  };

  const controller = new AbortController();
  const timeoutId = setTimeout(() => controller.abort(), 30000);

  try {
    const headers = {
      accept: "application/json, text/event-stream",
      "content-type": "application/json",
    };

    const response = await fetch(`${API_CONFIG.BASE_URL}${API_CONFIG.ENDPOINTS.CONTEXT}`, {
      method: "POST",
      headers,
      body: JSON.stringify(codeRequest),
      signal: AbortSignal.any([controller.signal, ctx.abort]),
    });

    clearTimeout(timeoutId);

    if (!response.ok) {
      const errorText = await response.text();
      throw new Error(`Code search error (${response.status}): ${errorText}`);
    }

    const responseText = await response.text();

    // Parse SSE response
    const lines = responseText.split("\n");
    for (const line of lines) {
      if (line.startsWith("data: ")) {
        const data = JSON.parse(line.substring(6));
        if (data.result && data.result.content && data.result.content.length > 0) {
          return {
            output: data.result.content[0].text,
            title: `Code search: ${params.query}`,
            metadata: {},
          };
        }
      }
    }

    return {
      output:
        "No code snippets or documentation found. Please try a different query, be more specific about the library or programming concept, or check the spelling of framework names.",
      title: `Code search: ${params.query}`,
      metadata: {},
    };
  } catch (error) {
    clearTimeout(timeoutId);

    if (error instanceof Error && error.name === "AbortError") {
      throw new Error("Code search request timed out");
    }

    throw error;
  }
};
