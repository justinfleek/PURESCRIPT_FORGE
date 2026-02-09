// FFI for Forge.Server.Routes.Tui
// 1:1 parity with opencode-dev/packages/opencode/src/server/routes/tui.ts

import { Bus } from "../../bus/Index.js";

// TUI state
let tuiState = {
  mode: "normal",
  focus: "input",
  prompt: "",
};

// Get TUI state
export const getFFI = async () => {
  try {
    return { tag: "Right", value: tuiState };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Update TUI state
export const updateFFI = (updates) => async () => {
  try {
    tuiState = { ...tuiState, ...updates };
    Bus.publish("tui.updated", { state: tuiState });
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Set TUI mode
export const setModeFFI = (mode) => async () => {
  try {
    tuiState.mode = mode;
    Bus.publish("tui.mode", { mode });
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Set TUI focus
export const setFocusFFI = (focus) => async () => {
  try {
    tuiState.focus = focus;
    Bus.publish("tui.focus", { focus });
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
