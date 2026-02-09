// FFI stubs for Doom.purs
// js-dos integration - these would be implemented with actual js-dos API calls

export const initDosbox = function(onError, onSuccess) {
  onSuccess({ tag: "Right", value0: {} });
  return function(cancelError, onCancelerError, onCancelerSuccess) {
    onCancelerSuccess();
  };
};

export const createEmulator = function(canvasId) {
  return function(onError, onSuccess) {
    onSuccess({ tag: "Right", value0: {} });
    return function(cancelError, onCancelerError, onCancelerSuccess) {
      onCancelerSuccess();
    };
  };
};

export const loadDoom = function(wadUrl) {
  return function(onError, onSuccess) {
    onSuccess({ tag: "Right", value0: {} });
    return function(cancelError, onCancelerError, onCancelerSuccess) {
      onCancelerSuccess();
    };
  };
};

export const sendKey = function(key) {
  return function(pressed) {
    return function() {
      // Would send key to js-dos emulator
    };
  };
};

export const pauseEmulator = function() {
  // Would pause the js-dos emulator
};

export const resumeEmulator = function() {
  // Would resume the js-dos emulator
};

export const stopEmulator = function() {
  // Would stop the js-dos emulator
};

export const saveState = function(onError, onSuccess) {
  onSuccess({ tag: "Right", value0: "saved" });
  return function(cancelError, onCancelerError, onCancelerSuccess) {
    onCancelerSuccess();
  };
};

export const loadState = function(onError, onSuccess) {
  onSuccess({ tag: "Right", value0: "loaded" });
  return function(cancelError, onCancelerError, onCancelerSuccess) {
    onCancelerSuccess();
  };
};

export const setVolume = function(volume) {
  return function() {
    // Would set volume on js-dos emulator
  };
};
