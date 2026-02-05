// Main Handler FFI
// Helper functions for extracting messages from requests and responses
// Encryption key management and message storage

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

// Get session encryption key
// Derives key from session ID and user secret for end-to-end encryption
// Returns Promise resolving to hex-encoded encryption key
export async function getSessionEncryptionKey(sessionId) {
  if (typeof sessionId !== "string" || sessionId.length === 0) {
    throw new Error("Invalid session ID");
  }
  
  // Get user secret from environment or secure storage
  // In production, this should come from secure key management
  const userSecret = process.env.USER_ENCRYPTION_SECRET || "default-secret-change-in-production";
  
  // Import encryption module
  const { deriveSessionKeyImpl } = await import("../MessageEncryption.js");
  
  // Derive session key
  return await deriveSessionKeyImpl(sessionId, userSecret);
}

// Store encrypted messages
// Saves encrypted messages to database/storage
// Messages are stored encrypted for total privacy
// Encrypted fields (encryptedContent, encryptionNonce, encryptionSalt) contain hex-encoded binary data
export async function storeEncryptedMessages(sessionId, inputMessages, outputMessages) {
  if (typeof sessionId !== "string" || sessionId.length === 0) {
    return;
  }
  
  // In production, this would save to database
  // For now, this is a placeholder that would integrate with your storage layer
  // Example: await db.saveEncryptedMessages(sessionId, inputMessages, outputMessages);
  
  // Messages are already encrypted by encryptMessageForStorage
  // Encrypted fields contain hex-encoded binary data and can be stored as strings
  console.log(`[ENCRYPTION] Storing ${inputMessages.length} input and ${outputMessages.length} output encrypted messages for session ${sessionId}`);
}

// Load encrypted messages from storage
// Returns array of encrypted CommonMessage objects
// Encrypted fields (encryptedContent, encryptionNonce, encryptionSalt) contain hex-encoded binary data
export async function loadEncryptedMessages(sessionId) {
  if (typeof sessionId !== "string" || sessionId.length === 0) {
    return [];
  }
  
  // In production, this would load from database
  // For now, this is a placeholder that would integrate with your storage layer
  // Example: return await db.loadEncryptedMessages(sessionId);
  
  // Returns empty array if no messages found
  return [];
}
