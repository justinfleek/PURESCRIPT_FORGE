"use strict";

var keyListener = null;
var resizeListener = null;

exports.subscribeKeyImpl = function(handler) {
  return function() {
    if (process.stdin.setEncoding) {
      process.stdin.setEncoding('utf8');
    }
    keyListener = function(data) {
      handler(data)();
    };
    process.stdin.on('data', keyListener);
    if (process.stdin.resume) {
      process.stdin.resume();
    }
  };
};

exports.subscribeResizeImpl = function(handler) {
  return function() {
    resizeListener = function() {
      var w = process.stdout.columns || 80;
      var h = process.stdout.rows || 24;
      handler(w)(h)();
    };
    process.stdout.on('resize', resizeListener);
  };
};

exports.unsubscribeImpl = function() {
  if (keyListener) {
    process.stdin.removeListener('data', keyListener);
    keyListener = null;
  }
  if (resizeListener) {
    process.stdout.removeListener('resize', resizeListener);
    resizeListener = null;
  }
  if (process.stdin.pause) {
    process.stdin.pause();
  }
};
