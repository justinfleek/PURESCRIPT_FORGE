/**
 * Canvas rendering FFI for Tetris game
 */

/**
 * Get canvas 2D context
 */
export const getCanvasContext = function (canvasId) {
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
export const clearCanvas = function (ctx) {
  return function () {
    if (!ctx) return;
    const canvas = ctx.canvas;
    ctx.clearRect(0, 0, canvas.width, canvas.height);
  };
};

/**
 * Draw filled rectangle
 */
export const drawRect = function (ctx) {
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
export const drawRectOutline = function (ctx) {
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
export const drawText = function (ctx) {
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
export const getCurrentTime = function () {
  return Date.now();
};
