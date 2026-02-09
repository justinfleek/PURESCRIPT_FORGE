// FFI for Sidepanel.Utils.Perf

// Ref values are mutable cells with a `value` property
// Initialized to null; the PureScript module should call Ref.new Map.empty
// to properly initialize these at runtime
export const navs = { value: null };
export const pending = { value: null };
export const active = { value: null };

// isDev: check environment
export const isDev = (typeof process !== "undefined" && process.env && process.env.NODE_ENV === "development") || false;

// performanceNow :: Effect Number
export const performanceNow = function () {
  if (typeof performance !== "undefined" && performance.now) {
    return performance.now();
  }
  return Date.now();
};

// generateUid :: Effect String
export const generateUid = function () {
  if (typeof crypto !== "undefined" && crypto.randomUUID) {
    return crypto.randomUUID();
  }
  return "id-" + Math.random().toString(36).substring(2, 11);
};

// jsonStringify :: forall a. a -> String
export const jsonStringify = function (obj) {
  try {
    return JSON.stringify(obj);
  } catch (e) {
    return "{}";
  }
};
