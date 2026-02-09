"use strict";

exports.onSignalImpl = function(sigName) {
  return function(handler) {
    return function() {
      process.on(sigName, function() {
        handler();
      });
    };
  };
};

exports.removeHandlerImpl = function(sigName) {
  return function() {
    process.removeAllListeners(sigName);
  };
};
