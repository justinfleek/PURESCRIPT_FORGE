// Forge.Server.Routes.File FFI
// 1:1 parity with opencode-dev/packages/opencode/src/server/routes/file.ts

const fs = require("fs/promises");

export const read = (path) => () =>
  fs.readFile(path, "utf-8").then(
    (c) => ({ tag: "Right", value: c }),
    (e) => ({ tag: "Left", value: e.message })
  );

export const write = (path) => (content) => () =>
  fs.writeFile(path, content).then(
    () => ({ tag: "Right", value: null }),
    (e) => ({ tag: "Left", value: e.message })
  );

export const list = (path) => () =>
  fs.readdir(path).then(
    (names) => ({ tag: "Right", value: names }),
    (e) => ({ tag: "Left", value: e.message })
  );
