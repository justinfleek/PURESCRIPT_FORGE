"use strict";

/**
 * Codex Plugin FFI
 * Integrates OpenAI Codex as a provider
 */

// | Initialize Codex plugin
exports.initCodexFFI = function (config) {
  return function (onError, onSuccess) {
    try {
      var apiKey = config.apiKey || process.env.OPENAI_API_KEY || null;
      if (!apiKey) {
        onSuccess({
          tag: "Left",
          value: "Codex API key not configured. Set OPENAI_API_KEY or provide apiKey in config.",
        });
        return function (c, ce, cs) { cs(); };
      }

      // Register Codex as available provider
      if (typeof process !== "undefined" && process.emit) {
        process.emit("forge:provider:registered", {
          id: "codex",
          name: "OpenAI Codex",
          type: "openai",
        });
      }

      onSuccess({ tag: "Right", value: undefined });
    } catch (e) {
      onSuccess({ tag: "Left", value: "Codex init failed: " + e.message });
    }

    return function (cancelError, onCancelerError, onCancelerSuccess) {
      onCancelerSuccess();
    };
  };
};

// | Check Codex availability
exports.isAvailableFFI = function (onError, onSuccess) {
  var hasKey = !!process.env.OPENAI_API_KEY;
  onSuccess(hasKey);
  return function (cancelError, onCancelerError, onCancelerSuccess) {
    onCancelerSuccess();
  };
};
