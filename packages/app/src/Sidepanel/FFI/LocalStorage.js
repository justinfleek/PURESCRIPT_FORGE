// | LocalStorage FFI Implementation
// | Provides type-safe access to browser localStorage

// | Get value from localStorage
export const getItem = function(key) {
  return function() {
    try {
      const value = localStorage.getItem(key);
      return value === null ? { tag: "Nothing" } : { tag: "Just", value: value };
    } catch (e) {
      return { tag: "Nothing" };
    }
  };
};

// | Set value in localStorage
export const setItem = function(key) {
  return function(value) {
    return function() {
      try {
        localStorage.setItem(key, value);
      } catch (e) {
        // Ignore quota exceeded errors silently
        // In production, could raise error or show notification
      }
    };
  };
};

// | Remove value from localStorage
export const removeItem = function(key) {
  return function() {
    try {
      localStorage.removeItem(key);
    } catch (e) {
      // Ignore errors
    }
  };
};

// | Clear all localStorage
export const clear = function() {
  return function() {
    try {
      localStorage.clear();
    } catch (e) {
      // Ignore errors
    }
  };
};

// | Get all keys from localStorage
export const getAllKeys = function() {
  return function() {
    try {
      const keys = [];
      for (let i = 0; i < localStorage.length; i++) {
        keys.push(localStorage.key(i));
      }
      return keys;
    } catch (e) {
      return [];
    }
  };
};
