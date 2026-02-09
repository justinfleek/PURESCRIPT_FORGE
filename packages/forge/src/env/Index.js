// Forge.Env.Index FFI - Environment variable utilities

// Get environment variable
export const getEnvFFI = (key) => () => {
  const value = process.env[key];
  return value !== undefined ? value : null;
};

// Set environment variable
export const setEnvFFI = (key) => (value) => () => {
  process.env[key] = value;
};

// Unset environment variable
export const unsetEnvFFI = (key) => () => {
  delete process.env[key];
};

// Parse integer
export const parseIntFFI = (s) => {
  const n = parseInt(s, 10);
  return isNaN(n) ? 0 : n;
};
