// FFI for Sidepanel.Utils.Persist
import { Ref } from "effect";

const _cache = { current: new Map() };
const _cacheTotal = { current: 0 };
const _fallbackDisabled = { current: false };

export const cache = _cache;
export const cacheTotal = _cacheTotal;
export const fallbackDisabled = _fallbackDisabled;

export const isQuotaErrorImpl = function(err) {
  if (err && typeof err === "object") {
    return err.name === "QuotaExceededError" || err.code === 22;
  }
  return false;
};

export const evict = function(storage) {
  return function(key) {
    return function() {
      try {
        if (typeof localStorage !== "undefined") {
          localStorage.removeItem(key);
        }
        return true;
      } catch (e) {
        return false;
      }
    };
  };
};

export const writeToStorage = function(key) {
  return function(value) {
    return function() {
      try {
        if (typeof localStorage !== "undefined") {
          localStorage.setItem(key, value);
        }
        return true;
      } catch (e) {
        return false;
      }
    };
  };
};

export const mergeImpl = function(defaults) {
  return function(value) {
    if (typeof defaults === "object" && typeof value === "object" && defaults !== null && value !== null) {
      return Object.assign({}, defaults, value);
    }
    return value;
  };
};

export const parseJson = function(str) {
  try {
    var result = JSON.parse(str);
    return { constructor: { name: "Just" }, value0: result };
  } catch (e) {
    return { constructor: { name: "Nothing" } };
  }
};

export const jsonStringify = function(value) {
  return JSON.stringify(value);
};

export const checksum = function(str) {
  var hash = 0;
  for (var i = 0; i < str.length; i++) {
    var char = str.charCodeAt(i);
    hash = ((hash << 5) - hash) + char;
    hash = hash & hash;
  }
  return Math.abs(hash).toString(36);
};

export const take = function(n) {
  return function(str) {
    return str.slice(0, n);
  };
};

export const stringLength = function(str) {
  return str.length;
};

export const removePersistedImpl = function(maybeStorage) {
  return function(key) {
    return function() {
      try {
        if (typeof localStorage !== "undefined") {
          localStorage.removeItem(key);
        }
      } catch (e) {
        // ignore
      }
    };
  };
};

export const persistedImpl = function(target) {
  return function(storeTuple) {
    return {
      store: storeTuple.value0,
      setStore: storeTuple.value1,
      init: null,
      ready: function() { return true; }
    };
  };
};
