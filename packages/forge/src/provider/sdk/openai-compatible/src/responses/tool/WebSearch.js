// Forge.Provider.SDK.OpenAICompatible.Responses.Tool.WebSearch FFI

export const searchFFI = (query) => (numResults) => async () => {
  try {
    const maxResults = numResults > 0 ? numResults : 5;
    const url = 'https://api.duckduckgo.com/?q=' + encodeURIComponent(query) + '&format=json&no_html=1';

    const response = await fetch(url);
    if (!response.ok) {
      return { tag: 'Left', value: 'Search API error: ' + response.status };
    }

    const data = await response.json();
    const results = [];

    if (data.RelatedTopics) {
      for (const topic of data.RelatedTopics.slice(0, maxResults)) {
        if (topic.Text && topic.FirstURL) {
          results.push({
            title: topic.Text.substring(0, 100),
            url: topic.FirstURL,
            snippet: topic.Text
          });
        }
      }
    }

    return { tag: 'Right', value: results };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
