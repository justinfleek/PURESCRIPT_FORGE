// FFI for Forge.Util.Token
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/token.ts

export const CHARS_PER_TOKEN = 4;

export const estimate = (input) => {
  return Math.max(0, Math.round((input || "").length / CHARS_PER_TOKEN));
};
