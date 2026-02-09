"use strict";

// FFI for Bridge.Database.Sync

exports.getCurrentTimeMillis = function () {
  return Date.now();
};

exports["toNumber'"] = function (n) {
  return n;
};

exports.trySync = function (aff) {
  return function (onError, onSuccess) {
    try {
      aff(
        function (err) {
          onSuccess({ tag: "Left", value: String(err) });
        },
        function (result) {
          onSuccess({ tag: "Right", value: result });
        }
      );
    } catch (e) {
      onSuccess({ tag: "Left", value: String(e) });
    }
    return function (cancelError, onCancelError, onCancelSuccess) {
      onCancelSuccess();
    };
  };
};
