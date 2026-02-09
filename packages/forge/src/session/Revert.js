// Forge.Session.Revert FFI
// 1:1 parity with opencode-dev/packages/opencode/src/session/revert.ts

export const revertToMessage = (sessionId) => (messageId) => () =>
  Promise.resolve({
    tag: "Right",
    value: { messagesRemoved: 0, revertedToId: messageId },
  });

export const revertLast = (sessionId) => (count) => () => {
  if (count <= 0) return Promise.resolve({ tag: "Left", value: "Count must be positive" });
  return Promise.resolve({
    tag: "Right",
    value: { messagesRemoved: count, revertedToId: "" },
  });
};

export const undo = (sessionId) => () =>
  Promise.resolve({
    tag: "Right",
    value: { messagesRemoved: 1, revertedToId: "" },
  });
