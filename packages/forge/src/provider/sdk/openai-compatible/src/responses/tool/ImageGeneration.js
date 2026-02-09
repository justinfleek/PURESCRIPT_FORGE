// Forge.Provider.SDK.OpenAICompatible.Responses.Tool.ImageGeneration FFI

export const generateFFI = (prompt) => (size) => (quality) => (style) => async () => {
  try {
    const apiKey = process.env.OPENAI_API_KEY;
    if (!apiKey) {
      return { tag: 'Left', value: 'OPENAI_API_KEY environment variable not set' };
    }

    const body = {
      prompt: prompt,
      n: 1,
      response_format: 'url'
    };
    if (size) body.size = size;
    if (quality) body.quality = quality;
    if (style) body.style = style;

    const response = await fetch('https://api.openai.com/v1/images/generations', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'Authorization': 'Bearer ' + apiKey
      },
      body: JSON.stringify(body)
    });

    if (!response.ok) {
      const errorText = await response.text();
      return { tag: 'Left', value: 'Image API error ' + response.status + ': ' + errorText };
    }

    const data = await response.json();
    const image = data.data && data.data[0];
    if (!image) {
      return { tag: 'Left', value: 'No image data in response' };
    }

    return {
      tag: 'Right',
      value: {
        url: image.url || '',
        revisedPrompt: image.revised_prompt || null
      }
    };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
