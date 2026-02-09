// Validation Utilities FFI Implementation


export const length = function(s) {
  return s.length;
};

export const contains = function(substr) {
  return function(str) {
    return str.indexOf(substr) !== -1;
  };
};
