// FFI for Forge.Util.Scrap
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/scrap.ts

export const foo = "42";
export const bar = 123;

export const dummyFunction = () => {
  console.log("This is a dummy function");
};

export const randomHelper = () => {
  return Math.random() > 0.5;
};
