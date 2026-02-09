// FFI for Bridge.FFI.Node.Process

export const getEnv = (key) => () => {
  const value = process.env[key];
  return value !== undefined ? value : null;
};

export const setEnv = (key) => (value) => () => {
  process.env[key] = value;
};

export const cwd = () => process.cwd();

export const platform = process.platform;
