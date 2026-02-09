// FFI bindings for Forge.Provider.Transform PureScript module

// Transform request to provider format
export const transformRequestFFI = (format) => (request) => {
  try {
    // Basic transformation - expands based on provider format
    let transformed = { ...request };
    
    switch (format) {
      case "anthropic":
        // Anthropic uses different field names
        transformed = {
          model: request.model,
          max_tokens: request.maxTokens || 4096,
          temperature: request.temperature,
          top_p: request.topP,
          top_k: request.topK,
          stop_sequences: request.stop,
          messages: request.messages.map(m => ({
            role: m.role,
            content: m.content || (m.contentParts ? m.contentParts : undefined)
          })),
          stream: request.stream,
          tools: request.tools,
          system: request.systemPrompt
        };
        break;
        
      case "openai":
      case "oa-compat":
        // OpenAI format (also used by many compatible providers)
        transformed = {
          model: request.model,
          max_tokens: request.maxTokens,
          temperature: request.temperature,
          top_p: request.topP,
          stop: request.stop,
          messages: request.systemPrompt 
            ? [{ role: "system", content: request.systemPrompt }, ...request.messages]
            : request.messages,
          stream: request.stream,
          tools: request.tools?.map(t => ({
            type: t.toolType,
            function: {
              name: t.functionName,
              description: t.functionDescription,
              parameters: t.functionParameters
            }
          })),
          tool_choice: request.toolChoice
        };
        break;
        
      case "google":
        // Google/Gemini format
        transformed = {
          model: request.model,
          generationConfig: {
            maxOutputTokens: request.maxTokens,
            temperature: request.temperature,
            topP: request.topP,
            topK: request.topK,
            stopSequences: request.stop
          },
          contents: request.messages.map(m => ({
            role: m.role === "assistant" ? "model" : m.role,
            parts: [{ text: m.content }]
          })),
          systemInstruction: request.systemPrompt ? { parts: [{ text: request.systemPrompt }] } : undefined
        };
        break;
        
      default:
        return { tag: "Left", value: `Unknown provider format: ${format}` };
    }
    
    return { tag: "Right", value: transformed };
  } catch (e) {
    return { tag: "Left", value: `Transform error: ${e.message}` };
  }
};

// Transform response from provider format to common format
export const transformResponseFFI = (format) => (json) => {
  try {
    let response;
    
    switch (format) {
      case "anthropic":
        response = {
          id: json.id,
          object: "chat.completion",
          created: Math.floor(Date.now() / 1000),
          model: json.model,
          choices: [{
            index: 0,
            message: {
              role: "assistant",
              content: json.content?.[0]?.text,
              toolCalls: json.content?.filter(c => c.type === "tool_use").map(t => ({
                id: t.id,
                toolType: "function",
                functionName: t.name,
                functionArguments: JSON.stringify(t.input)
              }))
            },
            finishReason: json.stop_reason === "end_turn" ? "stop" : json.stop_reason
          }],
          usage: {
            inputTokens: json.usage?.input_tokens,
            outputTokens: json.usage?.output_tokens,
            cacheReadInputTokens: json.usage?.cache_read_input_tokens,
            cacheCreationInputTokens: json.usage?.cache_creation_input_tokens
          }
        };
        break;
        
      case "openai":
      case "oa-compat":
        response = {
          id: json.id,
          object: json.object,
          created: json.created,
          model: json.model,
          choices: json.choices?.map(c => ({
            index: c.index,
            message: {
              role: c.message?.role,
              content: c.message?.content,
              toolCalls: c.message?.tool_calls?.map(t => ({
                id: t.id,
                toolType: t.type,
                functionName: t.function?.name,
                functionArguments: t.function?.arguments
              }))
            },
            finishReason: c.finish_reason
          })),
          usage: {
            inputTokens: json.usage?.prompt_tokens,
            outputTokens: json.usage?.completion_tokens,
            totalTokens: json.usage?.total_tokens
          }
        };
        break;
        
      case "google":
        response = {
          id: `google-${Date.now()}`,
          object: "chat.completion",
          created: Math.floor(Date.now() / 1000),
          model: json.modelVersion || "gemini",
          choices: json.candidates?.map((c, i) => ({
            index: i,
            message: {
              role: "assistant",
              content: c.content?.parts?.[0]?.text,
              toolCalls: c.content?.parts?.filter(p => p.functionCall).map(p => ({
                id: `call-${Date.now()}-${i}`,
                toolType: "function",
                functionName: p.functionCall?.name,
                functionArguments: JSON.stringify(p.functionCall?.args)
              }))
            },
            finishReason: c.finishReason?.toLowerCase()
          })),
          usage: {
            inputTokens: json.usageMetadata?.promptTokenCount,
            outputTokens: json.usageMetadata?.candidatesTokenCount,
            totalTokens: json.usageMetadata?.totalTokenCount
          }
        };
        break;
        
      default:
        return { tag: "Left", value: `Unknown provider format: ${format}` };
    }
    
    return { tag: "Right", value: response };
  } catch (e) {
    return { tag: "Left", value: `Transform error: ${e.message}` };
  }
};

// Transform streaming chunk from provider format
export const transformChunkFFI = (format) => (json) => {
  try {
    let chunk;
    
    switch (format) {
      case "anthropic":
        if (json.type === "content_block_delta") {
          chunk = {
            id: json.index?.toString() || "0",
            object: "chat.completion.chunk",
            created: Math.floor(Date.now() / 1000),
            model: "",
            choices: [{
              index: 0,
              delta: {
                content: json.delta?.text
              },
              finishReason: null
            }]
          };
        } else if (json.type === "message_stop") {
          chunk = {
            id: "stop",
            object: "chat.completion.chunk",
            created: Math.floor(Date.now() / 1000),
            model: "",
            choices: [{
              index: 0,
              delta: {},
              finishReason: "stop"
            }]
          };
        } else {
          chunk = {
            id: json.type,
            object: "chat.completion.chunk",
            created: Math.floor(Date.now() / 1000),
            model: json.message?.model || "",
            choices: [{
              index: 0,
              delta: {},
              finishReason: null
            }],
            usage: json.message?.usage ? {
              inputTokens: json.message.usage.input_tokens,
              outputTokens: json.message.usage.output_tokens
            } : null
          };
        }
        break;
        
      case "openai":
      case "oa-compat":
        chunk = {
          id: json.id,
          object: json.object,
          created: json.created,
          model: json.model,
          choices: json.choices?.map(c => ({
            index: c.index,
            delta: {
              role: c.delta?.role,
              content: c.delta?.content,
              toolCalls: c.delta?.tool_calls?.map(t => ({
                index: t.index,
                id: t.id,
                toolType: t.type,
                functionName: t.function?.name,
                functionArguments: t.function?.arguments
              }))
            },
            finishReason: c.finish_reason
          })),
          usage: json.usage ? {
            inputTokens: json.usage.prompt_tokens,
            outputTokens: json.usage.completion_tokens
          } : null
        };
        break;
        
      case "google":
        chunk = {
          id: `chunk-${Date.now()}`,
          object: "chat.completion.chunk",
          created: Math.floor(Date.now() / 1000),
          model: json.modelVersion || "gemini",
          choices: json.candidates?.map((c, i) => ({
            index: i,
            delta: {
              content: c.content?.parts?.[0]?.text
            },
            finishReason: c.finishReason?.toLowerCase()
          }))
        };
        break;
        
      default:
        return { tag: "Left", value: `Unknown provider format: ${format}` };
    }
    
    return { tag: "Right", value: chunk };
  } catch (e) {
    return { tag: "Left", value: `Transform error: ${e.message}` };
  }
};
