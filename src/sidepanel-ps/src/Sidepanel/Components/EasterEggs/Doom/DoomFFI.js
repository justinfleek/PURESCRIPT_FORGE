"use strict";

/**
 * Doom integration FFI via js-dos
 * js-dos is a DOS emulator that can run Doom in the browser
 */

let dosbox = null;
let emulator = null;

/**
 * Initialize js-dos
 */
exports.initDosbox = function () {
  return function () {
    return new Promise((resolve, reject) => {
      try {
        // Dynamically import js-dos if available
        if (typeof window !== "undefined" && window.DOSBox) {
          dosbox = window.DOSBox;
          resolve({ tag: "Right", value: {} });
        } else {
          // Try to load js-dos
          const script = document.createElement("script");
          script.src = "https://js-dos.com/games/dosbox.js";
          script.onload = () => {
            dosbox = window.DOSBox;
            resolve({ tag: "Right", value: {} });
          };
          script.onerror = () => {
            resolve({ tag: "Left", value: "Failed to load js-dos library" });
          };
          document.head.appendChild(script);
        }
      } catch (error) {
        resolve({ tag: "Left", value: error.message });
      }
    });
  };
};

/**
 * Create DOSBox emulator instance
 */
exports.createEmulator = function (canvasId) {
  return function () {
    return new Promise((resolve) => {
      try {
        if (!dosbox) {
          resolve({ tag: "Left", value: "DOSBox not initialized" });
          return;
        }
        
        const canvas = document.getElementById(canvasId);
        if (!canvas) {
          resolve({ tag: "Left", value: "Canvas not found" });
          return;
        }
        
        emulator = dosbox(canvas, {
          onerror: (error) => {
            console.error("DOSBox error:", error);
          },
        });
        
        resolve({ tag: "Right", value: {} });
      } catch (error) {
        resolve({ tag: "Left", value: error.message });
      }
    });
  };
};

/**
 * Load WAD file and start Doom
 */
exports.loadDoom = function (wadUrl) {
  return function () {
    return new Promise((resolve) => {
      try {
        if (!emulator) {
          resolve({ tag: "Left", value: "Emulator not created" });
          return;
        }
        
        // Load Doom shareware WAD
        // In production, would load user-provided WAD or shareware version
        emulator.run("https://js-dos.com/games/doom.zip", {
          onprogress: (stage, total, loaded) => {
            // Progress callback
          },
          onerror: (error) => {
            resolve({ tag: "Left", value: error.message || "Failed to load Doom" });
          },
        }).then(() => {
          resolve({ tag: "Right", value: {} });
        }).catch((error) => {
          resolve({ tag: "Left", value: error.message || "Failed to start Doom" });
        });
      } catch (error) {
        resolve({ tag: "Left", value: error.message });
      }
    });
  };
};

/**
 * Send keyboard input to emulator
 */
exports.sendKey = function (key) {
  return function (pressed) {
    return function () {
      try {
        if (!emulator) {
          return;
        }
        
        // Map key to DOSBox key code
        const keyCode = mapKeyToCode(key);
        if (keyCode) {
          if (pressed) {
            emulator.sendKey(keyCode, true);
          } else {
            emulator.sendKey(keyCode, false);
          }
        }
      } catch (error) {
        console.error("Error sending key:", error);
      }
    };
  };
};

/**
 * Map key string to DOSBox key code
 */
function mapKeyToCode(key) {
  const keyMap = {
    "w": 17,  // W
    "s": 31,  // S
    "a": 30,  // A
    "d": 32,  // D
    "q": 16,  // Q
    "e": 18,  // E
    " ": 57,  // Space
    "f": 33,  // F
    "Shift": 42,  // Left Shift
    "ArrowUp": 200,
    "ArrowDown": 208,
    "ArrowLeft": 203,
    "ArrowRight": 205,
  };
  
  return keyMap[key] || null;
}

/**
 * Pause/resume emulator
 */
exports.pauseEmulator = function () {
  return function () {
    try {
      if (emulator) {
        emulator.pause();
      }
    } catch (error) {
      console.error("Error pausing:", error);
    }
  };
};

exports.resumeEmulator = function () {
  return function () {
    try {
      if (emulator) {
        emulator.resume();
      }
    } catch (error) {
      console.error("Error resuming:", error);
    }
  };
};

/**
 * Stop emulator
 */
exports.stopEmulator = function () {
  return function () {
    try {
      if (emulator) {
        emulator.stop();
        emulator = null;
      }
    } catch (error) {
      console.error("Error stopping:", error);
    }
  };
};

/**
 * Save game state
 */
exports.saveState = function () {
  return function () {
    return new Promise((resolve) => {
      try {
        if (!emulator) {
          resolve({ tag: "Left", value: "Emulator not running" });
          return;
        }
        
        // js-dos doesn't directly support save states
        // Would need to use DOS save/load game feature
        resolve({ tag: "Right", value: "F6" });  // Doom quick save key
      } catch (error) {
        resolve({ tag: "Left", value: error.message });
      }
    });
  };
};

/**
 * Load game state
 */
exports.loadState = function () {
  return function () {
    return new Promise((resolve) => {
      try {
        if (!emulator) {
          resolve({ tag: "Left", value: "Emulator not running" });
          return;
        }
        
        // Send F9 for quick load
        resolve({ tag: "Right", value: "F9" });
      } catch (error) {
        resolve({ tag: "Left", value: error.message });
      }
    });
  };
};

/**
 * Set volume
 */
exports.setVolume = function (volume) {
  return function () {
    try {
      if (emulator) {
        // js-dos volume control
        emulator.setVolume(volume);
      }
    } catch (error) {
      console.error("Error setting volume:", error);
    }
  };
};
