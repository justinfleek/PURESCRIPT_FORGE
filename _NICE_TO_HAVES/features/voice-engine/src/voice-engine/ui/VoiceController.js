/**
 * Voice Controller FFI
 *
 * Web Speech API bindings for PureScript.
 * Provides speech recognition (STT) and synthesis (TTS).
 */

// Check for browser support
const SpeechRecognition =
  window.SpeechRecognition ||
  window.webkitSpeechRecognition ||
  null;

const SpeechSynthesis = window.speechSynthesis || null;

// Speech Recognition FFI

export const createSpeechRecognition = function() {
  if (!SpeechRecognition) {
    console.warn('Speech Recognition not supported in this browser');
    return null;
  }

  try {
    const recognition = new SpeechRecognition();
    return recognition;
  } catch (e) {
    console.error('Failed to create SpeechRecognition:', e);
    return null;
  }
};

export const startRecognition = function(recognition) {
  return function() {
    try {
      recognition.start();
    } catch (e) {
      // Already started, ignore
    }
  };
};

export const stopRecognition = function(recognition) {
  return function() {
    try {
      recognition.stop();
    } catch (e) {
      // Already stopped, ignore
    }
  };
};

export const setOnResult = function(recognition) {
  return function(callback) {
    return function() {
      recognition.onresult = function(event) {
        const last = event.results.length - 1;
        const transcript = event.results[last][0].transcript;
        callback(transcript)();
      };
    };
  };
};

export const setOnError = function(recognition) {
  return function(callback) {
    return function() {
      recognition.onerror = function(event) {
        callback(event.error)();
      };
    };
  };
};

export const setOnEnd = function(recognition) {
  return function(callback) {
    return function() {
      recognition.onend = function() {
        callback();
      };
    };
  };
};

export const setContinuous = function(recognition) {
  return function(value) {
    return function() {
      recognition.continuous = value;
    };
  };
};

export const setInterimResults = function(recognition) {
  return function(value) {
    return function() {
      recognition.interimResults = value;
    };
  };
};

export const setLanguage = function(recognition) {
  return function(lang) {
    return function() {
      recognition.lang = lang;
    };
  };
};

// Speech Synthesis FFI

export const getSpeechSynthesis = function() {
  return SpeechSynthesis;
};

export const speak = function(synthesis) {
  return function(text) {
    return function() {
      if (!synthesis) {
        console.warn('Speech Synthesis not supported');
        return;
      }

      // Cancel any ongoing speech
      synthesis.cancel();

      const utterance = new SpeechSynthesisUtterance(text);

      // Configure voice
      utterance.rate = 1.0;
      utterance.pitch = 1.0;
      utterance.volume = 1.0;

      // Try to use a natural voice
      const voices = synthesis.getVoices();
      const preferredVoice = voices.find(v =>
        v.lang.startsWith('en') && v.name.includes('Natural')
      ) || voices.find(v => v.lang.startsWith('en'));

      if (preferredVoice) {
        utterance.voice = preferredVoice;
      }

      synthesis.speak(utterance);
    };
  };
};

export const cancelSpeech = function(synthesis) {
  return function() {
    if (synthesis) {
      synthesis.cancel();
    }
  };
};

export const isSpeaking = function(synthesis) {
  return function() {
    return synthesis ? synthesis.speaking : false;
  };
};

// Audio Level Detection (for orb visualization)

let audioContext = null;
let analyser = null;
let microphone = null;

export const startAudioCapture = function(onLevel) {
  return function() {
    if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {
      console.warn('Audio capture not supported');
      return;
    }

    navigator.mediaDevices.getUserMedia({ audio: true })
      .then(stream => {
        audioContext = new (window.AudioContext || window.webkitAudioContext)();
        analyser = audioContext.createAnalyser();
        microphone = audioContext.createMediaStreamSource(stream);

        analyser.smoothingTimeConstant = 0.8;
        analyser.fftSize = 256;

        microphone.connect(analyser);

        const dataArray = new Uint8Array(analyser.frequencyBinCount);

        function updateLevel() {
          if (!analyser) return;

          analyser.getByteFrequencyData(dataArray);

          // Calculate average level (0-1)
          let sum = 0;
          for (let i = 0; i < dataArray.length; i++) {
            sum += dataArray[i];
          }
          const average = sum / dataArray.length / 255;

          onLevel(average)();

          requestAnimationFrame(updateLevel);
        }

        updateLevel();
      })
      .catch(err => {
        console.error('Failed to capture audio:', err);
      });
  };
};

export const stopAudioCapture = function() {
  if (microphone) {
    microphone.disconnect();
    microphone = null;
  }
  if (audioContext) {
    audioContext.close();
    audioContext = null;
  }
  analyser = null;
};
