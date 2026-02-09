// Forge.Provider.SDK.OpenAICompatible.Provider FFI

export const completeFFI = (baseUrl) => (apiKey) => (model) => (prompt) => async () => {
  try {
    const url = baseUrl.replace(/\/$/, '') + '/chat/completions';
    const headers = {
      'Content-Type': 'application/json'
    };
    if (apiKey) {
      headers['Authorization'] = 'Bearer ' + apiKey;
    }

    const body = JSON.stringify({
      model: model || 'gpt-4',
      messages: [{ role: 'user', content: prompt }]
    });

    const response = await fetch(url, {
      method: 'POST',
      headers: headers,
      body: body
    });

    if (!response.ok) {
      const errorText = await response.text();
      return { tag: 'Left', value: 'API error ' + response.status + ': ' + errorText };
    }

    const data = await response.json();
    const content = data.choices && data.choices[0] && data.choices[0].message
      ? data.choices[0].message.content || ''
      : '';

    return { tag: 'Right', value: content };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
