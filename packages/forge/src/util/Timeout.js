// FFI for Forge.Util.Timeout
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/timeout.ts

export const withTimeout = (ms) => (promise) => () => {
  let timeout;
  return Promise.race([
    promise().then((result) => {
      clearTimeout(timeout);
      return result;
    }),
    new Promise((_, reject) => {
      timeout = setTimeout(() => {
        reject(new Error(`Operation timed out after ${ms}ms`));
      }, ms);
    }),
  ]);
};
