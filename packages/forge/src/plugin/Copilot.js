"use strict";

/**
 * Copilot Plugin FFI
 * Integrates GitHub Copilot as a provider
 */

// | Initialize Copilot plugin
exports.initCopilotFFI = function (config) {
  return function (onError, onSuccess) {
    try {
      // Validate API key
      var apiKey = config.apiKey || process.env.GITHUB_COPILOT_TOKEN || null;
      if (!apiKey) {
        onSuccess({
          tag: "Left",
          value: "Copilot API key not configured. Set GITHUB_COPILOT_TOKEN or provide apiKey in config.",
        });
        return function (c, ce, cs) { cs(); };
      }

      // Register Copilot as available provider
      if (typeof process !== "undefined" && process.emit) {
        process.emit("forge:provider:registered", {
          id: "copilot",
          name: "GitHub Copilot",
          type: "copilot",
        });
      }

      onSuccess({ tag: "Right", value: undefined });
    } catch (e) {
      onSuccess({ tag: "Left", value: "Copilot init failed: " + e.message });
    }

    return function (cancelError, onCancelerError, onCancelerSuccess) {
      onCancelerSuccess();
    };
  };
};

// | Check Copilot availability
exports.isAvailableFFI = function (onError, onSuccess) {
  var hasKey = !!(process.env.GITHUB_COPILOT_TOKEN || process.env.GITHUB_TOKEN);
  onSuccess(hasKey);
  return function (cancelError, onCancelerError, onCancelerSuccess) {
    onCancelerSuccess();
  };
};
