// FFI for Forge.Util.Defer
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/defer.ts

export const defer = (fn) => {
  return {
    dispose: () => {
      fn()();
    },
    asyncDispose: () => {
      return Promise.resolve(fn()());
    },
    [Symbol.dispose]() {
      fn()();
    },
    [Symbol.asyncDispose]() {
      return Promise.resolve(fn()());
    },
  };
};
