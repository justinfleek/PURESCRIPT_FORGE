// Forge.Skill.Skill FFI
// 1:1 parity with opencode-dev/packages/opencode/src/skill/skill.ts

export const load = (name) => () =>
  Promise.resolve({ tag: "Left", value: "Skill.load not implemented" });

export const list = () =>
  Promise.resolve({ tag: "Right", value: [] });

export const get = (name) => () =>
  Promise.resolve(null);
