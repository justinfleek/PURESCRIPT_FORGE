// Pino logger FFI - ES Module

// Helper: Explicit default value (replaces banned || pattern)
const explicitDefault = (value, defaultValue) => {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
};

// Note: Dynamic import or stub for pino - in Node.js this would be:
// import pino from 'pino';
// For now we'll create a stub that works in browser/Node
const createPinoLogger = (options) => {
  // In a real implementation, this would use actual pino
  // For now, return a console-based logger stub
  return {
    info: (obj, msg) => console.info(msg !== undefined ? msg : obj, obj),
    warn: (obj, msg) => console.warn(msg !== undefined ? msg : obj, obj),
    error: (obj, msg) => console.error(msg !== undefined ? msg : obj, obj),
    debug: (obj, msg) => console.debug(msg !== undefined ? msg : obj, obj),
  };
};

export const create = (options) => () => {
  return createPinoLogger({
    name: options.name,
    level: explicitDefault(options.level, "info"),
  });
};

export const info = (logger) => (msg) => () => {
  logger.info(msg);
};

export const infoFields = (logger) => (msg) => (fields) => () => {
  logger.info(JSON.parse(fields), msg);
};

export const warn = (logger) => (msg) => () => {
  logger.warn(msg);
};

export const warnFields = (logger) => (msg) => (fields) => () => {
  logger.warn(JSON.parse(fields), msg);
};

export const error = (logger) => (msg) => () => {
  logger.error(msg);
};

export const errorFields = (logger) => (msg) => (fields) => () => {
  logger.error(JSON.parse(fields), msg);
};

export const debug = (logger) => (msg) => () => {
  logger.debug(msg);
};

export const debugFields = (logger) => (msg) => (fields) => () => {
  logger.debug(JSON.parse(fields), msg);
};
