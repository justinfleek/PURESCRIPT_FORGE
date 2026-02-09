/**
 * Canvas rendering FFI for Pong game (reuses Tetris FFI functions)
 */
import { getCanvasContext as _getCanvasContext, clearCanvas as _clearCanvas, drawRect as _drawRect, drawText as _drawText } from "../Tetris/TetrisFFI.js";

/**
 * Get canvas 2D context
 */
export const getCanvasContext = _getCanvasContext;

/**
 * Clear canvas
 */
export const clearCanvas = _clearCanvas;

/**
 * Draw filled rectangle
 */
export const drawRect = _drawRect;

/**
 * Draw text
 */
export const drawText = _drawText;
