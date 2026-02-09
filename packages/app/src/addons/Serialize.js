// FFI for App.Addons.Serialize

export const newImpl = function() {
  return { _type: "SerializeAddon", _buffer: "" };
};

export const activateImpl = function(addon, terminal) {
  addon._terminal = terminal;
};

export const disposeImpl = function(addon) {
  addon._terminal = null;
  addon._buffer = "";
};

export const serializeImpl = function(addon, opts) {
  return "";
};

export const serializeAsTextImpl = function(addon, opts) {
  return "";
};

export const toNullable = function(maybe) {
  if (maybe.constructor && maybe.constructor.name === "Just") {
    return maybe.value0;
  }
  return null;
};

const _null = null;
export { _null as null };
