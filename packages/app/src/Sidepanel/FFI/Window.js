"use strict";

exports.getViewportWidth = function() {
  return function() {
    return window.innerWidth || document.documentElement.clientWidth || 0;
  };
};

exports.getViewportHeight = function() {
  return function() {
    return window.innerHeight || document.documentElement.clientHeight || 0;
  };
};
