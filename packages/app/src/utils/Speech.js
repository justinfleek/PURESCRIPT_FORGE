// FFI for Sidepanel.Utils.Speech

export const hasSpeechSupport = function() {
  return typeof window !== "undefined" &&
    (typeof window.SpeechRecognition !== "undefined" || typeof window.webkitSpeechRecognition !== "undefined");
};

export const createRecognitionInstance = function(opts) {
  return function() {
    var SpeechRecognition = window.SpeechRecognition || window.webkitSpeechRecognition;
    var recognition = new SpeechRecognition();
    recognition.continuous = true;
    recognition.interimResults = true;
    if (opts.lang && opts.lang.constructor && opts.lang.constructor.name === "Just") {
      recognition.lang = opts.lang.value0;
    }
    return recognition;
  };
};

export const startRecognition = function(recognition) {
  return function() {
    try {
      recognition.start();
    } catch (e) {
      // Already started
    }
  };
};

export const stopRecognition = function(recognition) {
  return function() {
    try {
      recognition.stop();
    } catch (e) {
      // Already stopped
    }
  };
};

export const trim = function(s) {
  return s.trim();
};

export const isEmpty = function(s) {
  return s.length === 0;
};

export const hasTrailingNonSpace = function(s) {
  return s.length > 0 && s[s.length - 1] !== " ";
};

export const startsWithPunctuation = function(s) {
  return /^[.,;:!?]/.test(s);
};

export const split = function(s) {
  return s.split(/\s+/).filter(function(x) { return x.length > 0; });
};

export const joinWith = function(sep) {
  return function(arr) {
    return arr.join(sep);
  };
};

export const length = function(arr) {
  return arr.length;
};

export const index = function(arr) {
  return function(i) {
    return arr[i];
  };
};

export const drop = function(n) {
  return function(arr) {
    return arr.slice(n);
  };
};
