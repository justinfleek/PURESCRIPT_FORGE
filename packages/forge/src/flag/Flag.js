// FFI for Forge.Flag.Flag
// 1:1 parity with opencode-dev/packages/opencode/src/flag/flag.ts

// Feature flags from environment
export const OPENCODE_DEBUG = process.env.OPENCODE_DEBUG === "true";
export const OPENCODE_CLIENT = process.env.OPENCODE_CLIENT || "cli";
export const OPENCODE_ENABLE_EXA = process.env.OPENCODE_ENABLE_EXA === "true";
export const OPENCODE_AUTO_SHARE = process.env.OPENCODE_AUTO_SHARE === "true";
export const OPENCODE_EXPERIMENTAL_LSP_TOOL = process.env.OPENCODE_EXPERIMENTAL_LSP_TOOL === "true";
export const OPENCODE_EXPERIMENTAL_PLAN_MODE = process.env.OPENCODE_EXPERIMENTAL_PLAN_MODE === "true";
export const OPENCODE_ENABLE_EXPERIMENTAL_MODELS = process.env.OPENCODE_ENABLE_EXPERIMENTAL_MODELS === "true";

// Flag namespace
export const Flag = {
  OPENCODE_DEBUG,
  OPENCODE_CLIENT,
  OPENCODE_ENABLE_EXA,
  OPENCODE_AUTO_SHARE,
  OPENCODE_EXPERIMENTAL_LSP_TOOL,
  OPENCODE_EXPERIMENTAL_PLAN_MODE,
  OPENCODE_ENABLE_EXPERIMENTAL_MODELS,
};

// PureScript FFI exports
export const getEnvFFI = (key) => () => {
  const value = process.env[key];
  return value !== undefined ? value : null;
};

export const setEnvFFI = (key) => (value) => () => {
  process.env[key] = value;
};

export const getAllEnvKeysFFI = () => {
  return Object.keys(process.env);
};

export const getDebugFFI = () => OPENCODE_DEBUG;
export const getClientFFI = () => OPENCODE_CLIENT;
export const getEnableExaFFI = () => OPENCODE_ENABLE_EXA;
