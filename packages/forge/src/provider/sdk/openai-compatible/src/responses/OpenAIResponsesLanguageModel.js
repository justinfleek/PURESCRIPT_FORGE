"use strict";

/**
 * OpenAI Responses Language Model FFI
 * Implements OpenAI-compatible chat completion API calls
 */

// | Create chat completion (non-streaming)
exports.createChatCompletionFFI = function (config) {
  return function (request) {
    return function (onError, onSuccess) {
      (async function () {
        try {
          var url = config.baseUrl.replace(/\/$/, "") + "/v1/chat/completions";

          var body = {
            model: request.model,
            messages: request.messages.map(function (m) {
              var msg = { role: m.role, content: m.content };
              if (m.name) msg.name = m.name;
              if (m.toolCalls) msg.tool_calls = m.toolCalls;
              if (m.toolCallId) msg.tool_call_id = m.toolCallId;
              return msg;
            }),
            stream: false,
          };

          if (request.temperature != null) body.temperature = request.temperature;
          if (request.maxTokens != null) body.max_tokens = request.maxTokens;
          if (request.topP != null) body.top_p = request.topP;
          if (request.frequencyPenalty != null) body.frequency_penalty = request.frequencyPenalty;
          if (request.presencePenalty != null) body.presence_penalty = request.presencePenalty;
          if (request.stop != null) body.stop = request.stop;
          if (request.tools != null) body.tools = request.tools;

          var response = await fetch(url, {
            method: "POST",
            headers: {
              "Content-Type": "application/json",
              "Authorization": "Bearer " + config.apiKey,
            },
            body: JSON.stringify(body),
          });

          if (!response.ok) {
            var errorText = await response.text();
            onSuccess({
              tag: "Left",
              value: "HTTP " + response.status + ": " + errorText,
            });
            return;
          }

          var data = await response.json();
          onSuccess({
            tag: "Right",
            value: {
              id: data.id || "",
              object: data.object || "chat.completion",
              created: data.created || 0,
              model: data.model || request.model,
              choices: (data.choices || []).map(function (c) {
                return {
                  index: c.index || 0,
                  message: {
                    role: c.message.role || "assistant",
                    content: c.message.content || "",
                    name: c.message.name || null,
                    toolCalls: c.message.tool_calls || null,
                    toolCallId: c.message.tool_call_id || null,
                  },
                  finishReason: c.finish_reason || null,
                };
              }),
              usage: data.usage
                ? {
                    promptTokens: data.usage.prompt_tokens || 0,
                    completionTokens: data.usage.completion_tokens || 0,
                    totalTokens: data.usage.total_tokens || 0,
                  }
                : null,
            },
          });
        } catch (e) {
          onSuccess({
            tag: "Left",
            value: "Chat completion failed: " + e.message,
          });
        }
      })();

      return function (cancelError, onCancelerError, onCancelerSuccess) {
        onCancelerSuccess();
      };
    };
  };
};

// | Create streaming chat completion
exports.createStreamingChatCompletionFFI = function (config) {
  return function (request) {
    return function (onError, onSuccess) {
      (async function () {
        try {
          var url = config.baseUrl.replace(/\/$/, "") + "/v1/chat/completions";

          var body = {
            model: request.model,
            messages: request.messages.map(function (m) {
              var msg = { role: m.role, content: m.content };
              if (m.name) msg.name = m.name;
              if (m.toolCalls) msg.tool_calls = m.toolCalls;
              if (m.toolCallId) msg.tool_call_id = m.toolCallId;
              return msg;
            }),
            stream: true,
          };

          if (request.temperature != null) body.temperature = request.temperature;
          if (request.maxTokens != null) body.max_tokens = request.maxTokens;
          if (request.tools != null) body.tools = request.tools;

          var response = await fetch(url, {
            method: "POST",
            headers: {
              "Content-Type": "application/json",
              "Authorization": "Bearer " + config.apiKey,
            },
            body: JSON.stringify(body),
          });

          if (!response.ok) {
            var errorText = await response.text();
            onSuccess({
              tag: "Left",
              value: "HTTP " + response.status + ": " + errorText,
            });
            return;
          }

          // Read SSE stream
          var reader = response.body.getReader();
          var decoder = new TextDecoder();
          var buffer = "";

          while (true) {
            var readResult = await reader.read();
            if (readResult.done) break;

            buffer += decoder.decode(readResult.value, { stream: true });

            // Process SSE events
            var lines = buffer.split("\n");
            buffer = lines.pop(); // Keep incomplete line

            for (var i = 0; i < lines.length; i++) {
              var line = lines[i].trim();
              if (line.startsWith("data: ")) {
                var data = line.slice(6);
                if (data === "[DONE]") break;

                try {
                  var chunk = JSON.parse(data);
                  // Emit chunk event
                  if (typeof process !== "undefined" && process.emit) {
                    process.emit("forge:llm:chunk", chunk);
                  }
                } catch (e) {
                  // Skip malformed chunks
                }
              }
            }
          }

          onSuccess({ tag: "Right", value: undefined });
        } catch (e) {
          onSuccess({
            tag: "Left",
            value: "Streaming completion failed: " + e.message,
          });
        }
      })();

      return function (cancelError, onCancelerError, onCancelerSuccess) {
        onCancelerSuccess();
      };
    };
  };
};
