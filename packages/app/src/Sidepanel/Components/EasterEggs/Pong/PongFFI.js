"use strict";

/**
 * Canvas rendering FFI for Pong game (reuses Tetris FFI functions)
 */

const tetrisFFI = require("../Tetris/TetrisFFI.js");

/**
 * Get canvas 2D context
 */
exports.getCanvasContext = tetrisFFI.getCanvasContext;

/**
 * Clear canvas
 */
exports.clearCanvas = tetrisFFI.clearCanvas;

/**
 * Draw filled rectangle
 */
exports.drawRect = tetrisFFI.drawRect;

/**
 * Draw text
 */
exports.drawText = tetrisFFI.drawText;
