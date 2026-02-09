// Forge.Provider.SDK.OpenAICompatible.Responses.Tool.WebSearchPreview FFI

export const previewFFI = (url) => async () => {
  try {
    const response = await fetch(url, {
      headers: { 'User-Agent': 'ForgeBot/1.0' }
    });

    if (!response.ok) {
      return { tag: 'Left', value: 'Fetch error: ' + response.status };
    }

    const html = await response.text();

    const titleMatch = html.match(/<title[^>]*>([^<]+)<\/title>/i);
    const title = titleMatch ? titleMatch[1].trim() : null;

    const descMatch = html.match(/<meta[^>]*name=["']description["'][^>]*content=["']([^"']+)["']/i)
                   || html.match(/<meta[^>]*content=["']([^"']+)["'][^>]*name=["']description["']/i);
    const description = descMatch ? descMatch[1].trim() : null;

    const textContent = html
      .replace(/<script[^>]*>[\s\S]*?<\/script>/gi, '')
      .replace(/<style[^>]*>[\s\S]*?<\/style>/gi, '')
      .replace(/<[^>]+>/g, ' ')
      .replace(/\s+/g, ' ')
      .trim()
      .substring(0, 5000);

    return { tag: 'Right', value: { title, description, content: textContent } };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
