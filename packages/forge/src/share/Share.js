// Forge.Share.Share FFI
// 1:1 parity with opencode-dev/packages/opencode/src/share/share.ts

const URL = process.env.OPENCODE_API ?? "https://api.opencode.ai";
const disabled = process.env.OPENCODE_DISABLE_SHARE === "true" || process.env.OPENCODE_DISABLE_SHARE === "1";

export const share = (sessionId) => () => {
  if (disabled) return Promise.resolve({ tag: "Right", value: { url: "", expiresAt: null } });
  return fetch(`${URL}/share_create`, {
    method: "POST",
    body: JSON.stringify({ sessionID: sessionId }),
  })
    .then((r) => r.json())
    .then((x) => ({ tag: "Right", value: { url: x.url ?? "", expiresAt: null } }))
    .catch((e) => ({ tag: "Left", value: e.message }));
};

export const unshare = (sessionId) => () => {
  if (disabled) return Promise.resolve({ tag: "Right", value: null });
  return fetch(`${URL}/share_delete`, {
    method: "POST",
    body: JSON.stringify({ sessionID: sessionId, secret: "" }),
  })
    .then(() => ({ tag: "Right", value: null }))
    .catch((e) => ({ tag: "Left", value: e.message }));
};
