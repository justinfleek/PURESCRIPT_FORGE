"use strict";

/**
 * Canvas rendering FFI for Tetris game
 */

/**
 * Get canvas 2D context
 */
exports.getCanvasContext = function (canvasId) {
  return function () {
    const canvas = document.getElementById(canvasId);
    if (!canvas) {
      return null;
    }
    return canvas.getContext("2d");
  };
};

/**
 * Clear canvas
 */
exports.clearCanvas = function (ctx) {
  return function () {
    if (!ctx) return;
    const canvas = ctx.canvas;
    ctx.clearRect(0, 0, canvas.width, canvas.height);
  };
};

/**
 * Draw filled rectangle
 */
exports.drawRect = function (ctx) {
  return function (x) {
    return function (y) {
      return function (width) {
        return function (height) {
          return function (color) {
            return function () {
              if (!ctx) return;
              ctx.fillStyle = color;
              ctx.fillRect(x, y, width, height);
            };
          };
        };
      };
    };
  };
};

/**
 * Draw rectangle outline
 */
exports.drawRectOutline = function (ctx) {
  return function (x) {
    return function (y) {
      return function (width) {
        return function (height) {
          return function (color) {
            return function () {
              if (!ctx) return;
              ctx.strokeStyle = color;
              ctx.lineWidth = 1;
              ctx.strokeRect(x, y, width, height);
            };
          };
        };
      };
    };
  };
};

/**
 * Draw text
 */
exports.drawText = function (ctx) {
  return function (text) {
    return function (x) {
      return function (y) {
        return function (font) {
          return function (color) {
            return function () {
              if (!ctx) return;
              ctx.fillStyle = color;
              ctx.font = font;
              ctx.fillText(text, x, y);
            };
          };
        };
      };
    };
  };
};

/**
 * Get current timestamp in milliseconds
 */
exports.getCurrentTime = function () {
  return Date.now();
};
