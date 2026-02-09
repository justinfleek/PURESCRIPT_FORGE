// FFI for Sidepanel.Utils.Sound

export const alertSrc = function (n) {
  return "/sounds/alert-" + String(n).padStart(2, "0") + ".mp3";
};

export const bipBopSrc = function (n) {
  return "/sounds/bip-bop-" + String(n).padStart(2, "0") + ".mp3";
};

export const staplebopsSrc = function (n) {
  return "/sounds/staplebops-" + String(n).padStart(2, "0") + ".mp3";
};

export const nopeSrc = function (n) {
  return "/sounds/nope-" + String(n).padStart(2, "0") + ".mp3";
};

export const yupSrc = function (n) {
  return "/sounds/yup-" + String(n).padStart(2, "0") + ".mp3";
};

export const hasAudioSupport = function () {
  return typeof Audio !== "undefined";
};

export const createAudio = function (src) {
  return function () {
    return new Audio(src);
  };
};

export const playAudio = function (audio) {
  return function () {
    audio.play();
  };
};

export const stopAudio = function (audio) {
  return function () {
    audio.pause();
    audio.currentTime = 0;
  };
};
