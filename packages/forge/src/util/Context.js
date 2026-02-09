// FFI for Forge.Util.Context
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/context.ts

import { AsyncLocalStorage } from "async_hooks";

class NotFoundError extends Error {
  constructor(name) {
    super(`No context found for ${name}`);
    this.name = name;
  }
}

export const create = (name) => {
  const storage = new AsyncLocalStorage();
  return {
    use: () => {
      const result = storage.getStore();
      if (!result) {
        throw new NotFoundError(name);
      }
      return result;
    },
    provide: (value) => (fn) => () => {
      return storage.run(value, fn);
    },
  };
};

export const use = (context) => context.use;

export const provide = (context) => (value) => (fn) => () => {
  return context.provide(value)(fn)();
};
