// FFI for Forge.Util.Lock
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/lock.ts

const locks = new Map();

function get(key) {
  if (!locks.has(key)) {
    locks.set(key, {
      readers: 0,
      writer: false,
      waitingReaders: [],
      waitingWriters: [],
    });
  }
  return locks.get(key);
}

function process(key) {
  const lock = locks.get(key);
  if (!lock || lock.writer || lock.readers > 0) return;

  // Prioritize writers to prevent starvation
  if (lock.waitingWriters.length > 0) {
    const nextWriter = lock.waitingWriters.shift();
    nextWriter();
    return;
  }

  // Wake up all waiting readers
  while (lock.waitingReaders.length > 0) {
    const nextReader = lock.waitingReaders.shift();
    nextReader();
  }

  // Clean up empty locks
  if (lock.readers === 0 && !lock.writer && lock.waitingReaders.length === 0 && lock.waitingWriters.length === 0) {
    locks.delete(key);
  }
}

export const read = (key) => () => {
  const lock = get(key);

  return new Promise((resolve) => {
    if (!lock.writer && lock.waitingWriters.length === 0) {
      lock.readers++;
      resolve({
        dispose: () => {
          lock.readers--;
          process(key);
        },
      });
    } else {
      lock.waitingReaders.push(() => {
        lock.readers++;
        resolve({
          dispose: () => {
            lock.readers--;
            process(key);
          },
        });
      });
    }
  });
};

export const write = (key) => () => {
  const lock = get(key);

  return new Promise((resolve) => {
    if (!lock.writer && lock.readers === 0) {
      lock.writer = true;
      resolve({
        dispose: () => {
          lock.writer = false;
          process(key);
        },
      });
    } else {
      lock.waitingWriters.push(() => {
        lock.writer = true;
        resolve({
          dispose: () => {
            lock.writer = false;
            process(key);
          },
        });
      });
    }
  });
};

// Lock namespace for JS consumers
export const Lock = {
  read: async (key) => read(key)(),
  write: async (key) => write(key)(),
};
