/**
 * Error page FFI
 * Provides safe JSON serialization and type coercion for error handling
 */

// | Safely serialize a value to JSON, handling circular references and BigInt
export const safeJsonStringify = function (value) {
  try {
    var seen = new WeakSet();
    return JSON.stringify(value, function (key, val) {
      if (typeof val === "bigint") {
        return val.toString();
      }
      if (typeof val === "object" && val !== null) {
        if (seen.has(val)) {
          return "[Circular]";
        }
        seen.add(val);
      }
      return val;
    }, 2);
  } catch (e) {
    try {
      return String(value);
    } catch (e2) {
      return "[Object]";
    }
  }
};

// | Unsafe coerce between types (identity function)
export const unsafeCoerce = function (x) {
  return x;
};
