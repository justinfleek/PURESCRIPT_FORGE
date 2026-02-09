// Node.js Process FFI Implementation - ES Module

// | Get environment variable
export const getEnv = (envVar) => () => {
  // In browser/Node.js check for process.env
  const value = typeof process !== 'undefined' && process.env ? process.env[envVar] : undefined;
  return value === undefined || value === null
    ? null // PureScript Maybe Nothing
    : value; // PureScript Maybe Just
};

// | Generate session ID
export const generateSessionId = () => {
  // Simple random ID generation
  const arr = new Uint8Array(16);
  if (typeof crypto !== 'undefined' && crypto.getRandomValues) {
    crypto.getRandomValues(arr);
  } else {
    for (let i = 0; i < 16; i++) {
      arr[i] = Math.floor(Math.random() * 256);
    }
  }
  const hex = Array.from(arr).map(b => b.toString(16).padStart(2, '0')).join('');
  return "sess_" + hex;
};

// | Parse datetime string
// Returns DateTime structure compatible with PureScript Data.DateTime
export const parseDateTime = (timestamp) => () => {
  let date;
  // Try to parse the timestamp string
  if (timestamp && timestamp.trim() !== "") {
    date = new Date(timestamp);
    // If parsing failed, use current date
    if (isNaN(date.getTime())) {
      date = new Date();
    }
  } else {
    date = new Date();
  }
  
  // PureScript DateTime is an opaque type, but for FFI we return
  // a structure that matches the internal representation
  return {
    date: {
      year: date.getUTCFullYear(),
      month: date.getUTCMonth() + 1, // JavaScript months are 0-indexed
      day: date.getUTCDate()
    },
    time: {
      hour: date.getUTCHours(),
      minute: date.getUTCMinutes(),
      second: date.getUTCSeconds(),
      millisecond: date.getUTCMilliseconds()
    }
  };
};
