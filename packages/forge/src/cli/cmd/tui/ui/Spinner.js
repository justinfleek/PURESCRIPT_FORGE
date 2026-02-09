"use strict";

var spinnerInterval = null;
var currentFrame = 0;
var currentText = "";
var currentFrames = [];

exports.startImpl = function(frames) {
  return function(interval) {
    return function(text) {
      return function() {
        currentFrames = frames;
        currentText = text;
        currentFrame = 0;

        if (spinnerInterval) {
          clearInterval(spinnerInterval);
        }

        spinnerInterval = setInterval(function() {
          var frame = currentFrames[currentFrame % currentFrames.length];
          process.stdout.write('\r\x1b[2K' + frame + ' ' + currentText);
          currentFrame++;
        }, interval);
      };
    };
  };
};

exports.stopImpl = function() {
  if (spinnerInterval) {
    clearInterval(spinnerInterval);
    spinnerInterval = null;
  }
  process.stdout.write('\r\x1b[2K');
};

exports.setTextImpl = function(text) {
  return function() {
    currentText = text;
  };
};
