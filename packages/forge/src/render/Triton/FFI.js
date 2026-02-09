// Triton Inference Server FFI - HTTP/SSE streaming
// Provides deterministic PureScript implementation using HTTP API
"use strict";

/**
 * Stream inference via Server-Sent Events (SSE)
 *
 * Uses HTTP POST to Triton inference endpoint.
 * Accumulates response and returns final InferenceResponse.
 *
 * @param {string} url - Triton inference endpoint with ?stream=true
 * @param {string} requestBody - JSON-encoded request body
 * @returns {Function} Aff callback pattern
 */
exports.streamInference = function(url) {
  return function(requestBody) {
    return function(onError, onSuccess) {
      try {
        var fetchUrl = url.replace('?stream=true', '');

        var headers = { 'Content-Type': 'application/json' };
        var init = {
          method: 'POST',
          headers: headers,
          body: requestBody
        };

        globalThis.fetch(fetchUrl, init)
          .then(function(response) {
            return response.json();
          })
          .then(function(data) {
            // Parse Triton response
            var outputs = data.outputs;
            if (outputs === undefined || outputs === null) {
              outputs = [];
            }

            var text = '';
            for (var i = 0; i < outputs.length; i++) {
              if (outputs[i].name === 'text_output') {
                var outputData = outputs[i].data;
                if (outputData !== undefined && outputData !== null && outputData.length > 0) {
                  text = outputData[0];
                }
                break;
              }
            }

            var responseId = 'triton-response';
            if (data.id !== undefined && data.id !== null) {
              responseId = data.id;
            }

            var responseModel = 'triton';
            if (data.model !== undefined && data.model !== null) {
              responseModel = data.model;
            }

            // Return final response
            var inferResponse = {
              id: responseId,
              model: responseModel,
              text: text,
              finishReason: 'stop',
              usage: {
                promptTokens: 0,
                completionTokens: 0,
                totalTokens: 0,
                cachedTokens: null,
                timeToFirstToken: null,
                tokensPerSecond: null
              },
              logProbs: null
            };

            onSuccess({
              tag: 'Right',
              value: inferResponse
            });
          })
          .catch(function(error) {
            var errorMessage = error.message !== undefined && error.message !== null ? error.message : String(error);
            onSuccess({
              tag: 'Left',
              value: errorMessage
            });
          });
      } catch (e) {
        onSuccess({
          tag: 'Left',
          value: String(e)
        });
      }
      return function(cancelError, onCancelError, onCancelSuccess) {
        onCancelSuccess();
      };
    };
  };
};
