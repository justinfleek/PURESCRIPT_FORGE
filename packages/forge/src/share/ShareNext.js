// Forge.Share.ShareNext FFI
// 1:1 parity with opencode-dev/packages/opencode/src/share/share-next.ts

const disabled = process.env.OPENCODE_DISABLE_SHARE === "true" || process.env.OPENCODE_DISABLE_SHARE === "1";
const baseUrl = () => Promise.resolve(process.env.OPENCODE_ENTERPRISE_URL ?? "https://opncd.ai");

export const shareWithOptions = (sessionId) => (options) => () => {
  if (disabled) return Promise.resolve({ tag: "Right", value: "" });
  return baseUrl()
    .then((url) =>
      fetch(`${url}/api/share`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ sessionID: sessionId }),
      })
    )
    .then((r) => r.json())
    .then((x) => ({ tag: "Right", value: x.url ?? "" }))
    .catch((e) => ({ tag: "Left", value: e.message }));
};
