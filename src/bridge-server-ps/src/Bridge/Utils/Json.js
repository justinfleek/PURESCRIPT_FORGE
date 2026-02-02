// JSON Utilities FFI Implementation


export const parseJson = function(jsonStr) {
  return function() {
    try {
      var parsed = JSON.parse(jsonStr);
      return { tag: "Right", value: parsed };
    } catch (e) {
      var errorMessage = e.message !== undefined && e.message !== null ? e.message : "Parse error";
      return { tag: "Left", value: errorMessage };
    }
  };
};

export const hasField = function(obj) {
  return function(field) {
    return obj && typeof obj === "object" && field in obj;
  };
};

export const getField = function(obj) {
  return function(field) {
    if (obj && typeof obj === "object" && field in obj) {
      var value = obj[field];
      return value !== null && value !== undefined ? { tag: "Just", value: String(value) } : { tag: "Nothing" };
    }
    return { tag: "Nothing" };
  };
};

export const foldl = function(f) {
  return function(initial) {
    return function(arr) {
      var result = initial;
      for (var i = 0; i < arr.length; i++) {
        result = f(result)(arr[i]);
      }
      return result;
    };
  };
};
