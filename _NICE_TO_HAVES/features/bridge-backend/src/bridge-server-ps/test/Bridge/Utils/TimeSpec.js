// Test helpers for TimeSpec
"use strict";

exports.split = function(separator) {
  return function(str) {
    return str.split(separator);
  };
};

exports.countOccurrences = function(substring) {
  return function(str) {
    var count = 0;
    var index = 0;
    while ((index = str.indexOf(substring, index)) !== -1) {
      count++;
      index += substring.length;
    }
    return count;
  };
};

exports.shouldBeGreaterThan = function(expected) {
  return function(actual) {
    return actual > expected;
  };
};

exports.shouldBeGreaterThanOrEqual = function(expected) {
  return function(actual) {
    return actual >= expected;
  };
};

exports.endsWith = function(suffix) {
  return function(str) {
    return str.endsWith(suffix);
  };
};

exports.dropEnd = function(n) {
  return function(str) {
    if (n >= str.length) {
      return "";
    }
    return str.substring(0, str.length - n);
  };
};

exports.parseNumber = function(str) {
  var num = parseInt(str, 10);
  if (isNaN(num)) {
    return null;
  }
  return num;
};

exports.length = function(str) {
  return str.length;
};

exports.contains = function(substring) {
  return function(str) {
    return str.indexOf(substring) !== -1;
  };
};
