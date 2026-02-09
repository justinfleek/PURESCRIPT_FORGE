"use strict";

exports.getWidthImpl = function() {
  return process.stdout.columns || 80;
};

exports.getHeightImpl = function() {
  return process.stdout.rows || 24;
};

exports.isTTYImpl = function() {
  return process.stdout.isTTY === true;
};

exports.enableRawModeImpl = function() {
  if (process.stdin.setRawMode) {
    process.stdin.setRawMode(true);
  }
};

exports.disableRawModeImpl = function() {
  if (process.stdin.setRawMode) {
    process.stdin.setRawMode(false);
  }
};

exports.clearImpl = function() {
  process.stdout.write('\x1b[2J\x1b[H');
};

exports.moveCursorImpl = function(x) {
  return function(y) {
    return function() {
      process.stdout.write('\x1b[' + y + ';' + x + 'H');
    };
  };
};
