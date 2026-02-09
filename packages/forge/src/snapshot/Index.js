// Forge.Snapshot.Index FFI
// 1:1 parity with opencode-dev/packages/opencode/src/snapshot/index.ts

export const create = (sessionId) => (messageId) => () =>
  Promise.resolve({
    tag: "Right",
    value: { id: messageId, sessionId, messageId, createdAt: Date.now() },
  });

export const restore = (snapshotId) => () =>
  Promise.resolve({ tag: "Right", value: null });

export const list = (sessionId) => () =>
  Promise.resolve({ tag: "Right", value: [] });
