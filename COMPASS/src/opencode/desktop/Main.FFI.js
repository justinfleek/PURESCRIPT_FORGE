"use strict";

const { invoke } = require("@tauri-apps/api/core");
const { type: ostype } = require("@tauri-apps/plugin-os");

const OS_NAME = ostype();
const MAX_ZOOM_LEVEL = 10.0;
const MIN_ZOOM_LEVEL = 0.2;
const DEFAULT_ZOOM_LEVEL = 1.0;
const ZOOM_STEP = 0.2;

let currentZoomLevel = DEFAULT_ZOOM_LEVEL;

/**
 * Setup keyboard shortcuts for zoom
 */
exports.setupZoomKeyboardShortcuts = function () {
  window.addEventListener("keydown", function (event) {
    const modifierKey = OS_NAME === "macos" ? event.metaKey : event.ctrlKey;
    if (!modifierKey) return;

    if (event.key === "-") {
      currentZoomLevel = Math.max(currentZoomLevel - ZOOM_STEP, MIN_ZOOM_LEVEL);
      invoke("plugin:webview|set_webview_zoom", { value: currentZoomLevel }).catch(function () {
        return null;
      });
    } else if (event.key === "=" || event.key === "+") {
      currentZoomLevel = Math.min(currentZoomLevel + ZOOM_STEP, MAX_ZOOM_LEVEL);
      invoke("plugin:webview|set_webview_zoom", { value: currentZoomLevel }).catch(function () {
        return null;
      });
    } else if (event.key === "0") {
      currentZoomLevel = DEFAULT_ZOOM_LEVEL;
      invoke("plugin:webview|set_webview_zoom", { value: currentZoomLevel }).catch(function () {
        return null;
      });
    }
  });
};

/**
 * Restore saved zoom level
 */
exports.restoreZoomLevel = function () {
  const saved = localStorage.getItem("opencode:webview:zoom");
  if (saved !== null) {
    const zoom = parseFloat(saved);
    if (!isNaN(zoom) && zoom >= MIN_ZOOM_LEVEL && zoom <= MAX_ZOOM_LEVEL) {
      currentZoomLevel = zoom;
      invoke("plugin:webview|set_webview_zoom", { value: currentZoomLevel }).catch(function () {
        return null;
      });
    }
  }
  
  window.addEventListener("beforeunload", function () {
    localStorage.setItem("opencode:webview:zoom", String(currentZoomLevel));
  });
};
