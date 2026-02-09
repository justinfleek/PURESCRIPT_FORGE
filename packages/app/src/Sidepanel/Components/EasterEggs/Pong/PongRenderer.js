// FFI for Sidepanel.Components.EasterEggs.Pong.PongRenderer

export const getCanvasContext = function (canvasId) {
  return function () {
    var canvas = document.getElementById(canvasId);
    if (canvas && canvas.getContext) {
      var ctx = canvas.getContext("2d");
      if (ctx) {
        return ctx;
      }
    }
    return null;
  };
};

export const clearCanvas = function (ctx) {
  return function () {
    ctx.clearRect(0, 0, ctx.canvas.width, ctx.canvas.height);
  };
};

export const drawRect = function (ctx) {
  return function (x) {
    return function (y) {
      return function (w) {
        return function (h) {
          return function (color) {
            return function () {
              ctx.fillStyle = color;
              ctx.fillRect(x, y, w, h);
            };
          };
        };
      };
    };
  };
};

export const drawText = function (ctx) {
  return function (text) {
    return function (x) {
      return function (y) {
        return function (font) {
          return function (color) {
            return function () {
              ctx.font = font;
              ctx.fillStyle = color;
              ctx.fillText(text, x, y);
            };
          };
        };
      };
    };
  };
};
