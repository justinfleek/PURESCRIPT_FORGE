// FFI for App.Addons.Serialize.Spec
// Stub implementations for terminal testing (requires browser environment with ghostty-web)

import * as $Maybe from "../Data.Maybe/index.js";

export const loadGhosttyImpl = function() {
  return {};
};

export const createTerminalImpl = function(cols, rows, ghostty) {
  return { cols: cols, rows: rows, ghostty: ghostty, buffer: [] };
};

export const disposeTerminalImpl = function(terminal) {
  return;
};

export const loadAddonImpl = function(terminal, addon) {
  return;
};

export const openTerminalImpl = function(terminal) {
  return;
};

export const writeImpl = function(terminal, data) {
  return function() { return; };
};

export const resetTerminalImpl = function(terminal) {
  return;
};

export const getActiveBufferTypeImpl = function(terminal) {
  return "normal";
};

export const getBufferLineImpl = function(terminal, row) {
  return $Maybe.Nothing.value;
};

export const translateLineToStringImpl = function(line, trim) {
  return "";
};

export const getCellCharsImpl = function(line, col) {
  return "";
};

export const getCellIsBoldImpl = function(line, col) {
  return 0;
};

export const getCellIsItalicImpl = function(line, col) {
  return 0;
};

export const getCellIsUnderlineImpl = function(line, col) {
  return 0;
};

export const getCellFgColorImpl = function(line, col) {
  return 0;
};

export const getCellBgColorImpl = function(line, col) {
  return 0;
};

export const getCellCodeImpl = function(line, col) {
  return 0;
};
