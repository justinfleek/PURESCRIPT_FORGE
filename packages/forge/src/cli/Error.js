// Forge.CLI.Error FFI

// Print error to stderr
export const printErrorFFI = (str) => () => {
  console.error(str);
};
