"use strict";

/**
 * Server Event Bus FFI
 * Provides pub/sub event system for server-side events
 */

// Event subscribers
var subscribers = [];

// | Subscribe to server events
exports.subscribeFFI = function (callback) {
  return function (onError, onSuccess) {
    try {
      subscribers.push(callback);
      onSuccess({ tag: "Right", value: undefined });
    } catch (e) {
      onSuccess({ tag: "Left", value: "Failed to subscribe: " + e.message });
    }

    return function (cancelError, onCancelerError, onCancelerSuccess) {
      onCancelerSuccess();
    };
  };
};

// | Publish event to all subscribers
exports.publishFFI = function (event) {
  return function () {
    for (var i = 0; i < subscribers.length; i++) {
      try {
        subscribers[i](event)();
      } catch (e) {
        // Don't let one subscriber error break others
      }
    }
  };
};

// | Unsubscribe all
exports.unsubscribeFFI = function () {
  subscribers = [];
};
