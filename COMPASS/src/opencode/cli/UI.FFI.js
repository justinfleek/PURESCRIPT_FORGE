"use strict";

/**
 * CLI UI FFI
 * Provides terminal utilities
 */

// | Clear terminal screen
exports.clearTerminalScreen = function () {
  // ANSI escape code to clear screen and move cursor to top
  process.stdout.write("\x1b[2J\x1b[H");
};
