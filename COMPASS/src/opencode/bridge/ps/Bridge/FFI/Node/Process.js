// Node.js Process FFI Implementation
"use strict";

// | Get environment variable
exports.getEnv = function(envVar) {
  return function() {
    var value = process.env[envVar];
    return value === undefined || value === null
      ? { tag: "Nothing" }
      : { tag: "Just", value: value };
  };
};

// | Generate session ID
exports.generateSessionId = function() {
  return function() {
    const crypto = require("crypto");
    return "sess_" + crypto.randomBytes(16).toString("hex");
  };
};

// | Parse datetime string
// Returns DateTime structure compatible with PureScript Data.DateTime
exports.parseDateTime = function(timestamp) {
  return function() {
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
    // DateTime wraps Date and Time, where Date has year/month/day and Time has hour/minute/second/millisecond
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
};
