// Time Utilities FFI Implementation
"use strict";

exports.diffDateTime = function(target) {
  return function(now) {
    var targetMs = new Date(target).getTime();
    var nowMs = new Date(now).getTime();
    var diffMs = targetMs - nowMs;
    
    if (diffMs <= 0) {
      return { hours: 0, minutes: 0, seconds: 0, totalMs: 0.0 };
    }
    
    var hours = Math.floor(diffMs / (1000 * 60 * 60));
    var minutes = Math.floor((diffMs % (1000 * 60 * 60)) / (1000 * 60));
    var seconds = Math.floor((diffMs % (1000 * 60)) / 1000);
    
    return {
      hours: hours,
      minutes: minutes,
      seconds: seconds,
      totalMs: diffMs
    };
  };
};

exports.getCurrentDateTime = function() {
  return function() {
    var date = new Date();
    // Return DateTime structure matching PureScript Data.DateTime
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
