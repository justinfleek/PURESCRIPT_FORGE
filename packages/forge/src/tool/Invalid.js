// FFI for Forge.Tool.Invalid
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/invalid.ts

export const execute = (params) => async () => {
  return {
    title: "Invalid Tool",
    output: `The arguments provided to the tool are invalid: ${params.error}`,
    metadata: {},
  };
};
