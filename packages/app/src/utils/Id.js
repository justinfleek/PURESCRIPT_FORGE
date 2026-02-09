// FFI for Sidepanel.Utils.Id

// Module-level mutable state for monotonic ID generation
let _lastTimestamp = { value: 0 };
let _counter = { value: 0 };

export const lastTimestamp = _lastTimestamp;
export const counter = _counter;

// Generate random base62 string of given length
const base62Chars = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
export const randomBase62 = function (length) {
  let result = "";
  for (let i = 0; i < length; i++) {
    result += base62Chars.charAt(Math.floor(Math.random() * 62));
  }
  return result;
};

// Throw an error (returns Effect a)
export const throwError = function (msg) {
  return function () {
    throw new Error(msg);
  };
};

// Convert any value to Number
export const toNumber = function (x) {
  return Number(x);
};

// Convert Int (char code) to Char
export const toEnum = function (n) {
  return String.fromCharCode(n);
};
