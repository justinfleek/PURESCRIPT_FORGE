// FFI for Forge.Util.Lazy
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/lazy.ts

export const lazy = (fn) => {
  let value = undefined;
  let loaded = false;

  const result = {
    get: () => {
      if (loaded) return value;
      loaded = true;
      value = fn();
      return value;
    },
    reset: () => {
      loaded = false;
      value = undefined;
    }
  };

  return result;
};

export const reset = (lazyValue) => () => {
  lazyValue.reset();
};
