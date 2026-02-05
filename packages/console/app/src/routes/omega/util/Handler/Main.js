// Main Handler FFI
// Helper functions for extracting messages from requests and responses

// Extract messages from CommonRequest (PureScript type)
// CommonRequest has a messages field which is an array of CommonMessage
export function extractMessagesFromRequest(commonRequest) {
  if (typeof commonRequest !== "object" || commonRequest === null) {
    return [];
  }
  
  if (!Array.isArray(commonRequest.messages)) {
    return [];
  }
  
  return commonRequest.messages;
}

// Extract messages from JSON response
// Response format varies by provider, but typically has choices[].message
export function extractMessagesFromResponse(jsonValue) {
  if (typeof jsonValue !== "string") {
    return [];
  }
  
  try {
    const json = JSON.parse(jsonValue);
    
    if (typeof json !== "object" || json === null) {
      return [];
    }
    
    // OpenAI/OpenAI-compatible format: choices[].message
    if (Array.isArray(json.choices)) {
      const messages = [];
      for (const choice of json.choices) {
        if (choice && typeof choice.message === "object" && choice.message !== null) {
          const msg = choice.message;
          messages.push({
            role: typeof msg.role === "string" ? msg.role : "assistant",
            content: typeof msg.content === "string" ? msg.content : null,
            contentParts: null,
            toolCallId: null,
            toolCalls: Array.isArray(msg.tool_calls) ? msg.tool_calls : null,
          });
        }
      }
      return messages;
    }
    
    // Anthropic format: content[] array
    if (Array.isArray(json.content)) {
      const contentText = json.content
        .filter((part) => part && part.type === "text" && typeof part.text === "string")
        .map((part) => part.text)
        .join("");
      
      if (contentText.length > 0) {
        return [{
          role: "assistant",
          content: contentText,
          contentParts: null,
          toolCallId: null,
          toolCalls: null,
        }];
      }
    }
    
    return [];
  } catch (e) {
    return [];
  }
}
