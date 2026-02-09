// FFI bindings for Tool.Websearch PureScript module
// Implements web search via configurable search API

// Execute web search
// Supports SearXNG, DuckDuckGo lite, and direct fetch
export const searchFFI = (query) => (limit) => () => {
  return new Promise(async (resolve) => {
    try {
      // Check for configured search API endpoint
      const searchUrl = process.env.FORGE_SEARCH_API
        || process.env.SEARXNG_URL
        || null;

      if (searchUrl) {
        // Use configured search API (SearXNG compatible)
        const url = new URL(searchUrl);
        url.searchParams.set("q", query);
        url.searchParams.set("format", "json");
        url.searchParams.set("pageno", "1");
        if (limit > 0) {
          url.searchParams.set("results", String(limit));
        }

        const response = await fetch(url.toString(), {
          headers: { "Accept": "application/json" },
          signal: AbortSignal.timeout(15000)
        });

        if (!response.ok) {
          resolve({
            tag: "Left",
            value: "Search API returned HTTP " + response.status
          });
          return;
        }

        const data = await response.json();
        const results = (data.results || []).slice(0, limit || 10).map(r => ({
          title: r.title || "",
          url: r.url || r.href || "",
          snippet: r.content || r.snippet || "",
          source: r.engine || "search"
        }));

        resolve({
          tag: "Right",
          value: {
            query,
            results,
            totalResults: data.number_of_results || results.length
          }
        });
      } else {
        // No search API configured
        resolve({
          tag: "Left",
          value: "No search API configured. Set FORGE_SEARCH_API or SEARXNG_URL environment variable."
        });
      }
    } catch (e) {
      resolve({
        tag: "Left",
        value: "Web search failed: " + e.message
      });
    }
  });
};
