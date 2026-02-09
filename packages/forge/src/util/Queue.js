// FFI for Forge.Util.Queue
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/queue.ts

class AsyncQueue {
  constructor() {
    this.queue = [];
    this.resolvers = [];
  }

  push(item) {
    const resolve = this.resolvers.shift();
    if (resolve) resolve(item);
    else this.queue.push(item);
  }

  async next() {
    if (this.queue.length > 0) return this.queue.shift();
    return new Promise((resolve) => this.resolvers.push(resolve));
  }

  async *[Symbol.asyncIterator]() {
    while (true) yield await this.next();
  }
}

export const createQueue = () => new AsyncQueue();

export const push = (queue) => (item) => () => {
  queue.push(item);
};

export const next = (queue) => () => queue.next();

export const work = (concurrency) => (items) => (fn) => async () => {
  const pending = [...items];
  await Promise.all(
    Array.from({ length: concurrency }, async () => {
      while (true) {
        const item = pending.pop();
        if (item === undefined) return;
        await fn(item)();
      }
    })
  );
};
