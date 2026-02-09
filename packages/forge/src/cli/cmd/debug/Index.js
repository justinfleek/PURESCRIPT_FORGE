// Forge.CLI.Cmd.Debug.Index FFI

export const showHelpFFI = async () => {
  console.log('Available debug commands:');
  console.log('  agent    - Show agent debug info');
  console.log('  config   - Show configuration');
  console.log('  file     - Debug file operations');
  console.log('  lsp      - Show LSP status');
  console.log('  ripgrep  - Debug ripgrep operations');
  console.log('  scrap    - Scratch diagnostics');
  console.log('  skill    - Show skill info');
  console.log('  snapshot - Show runtime snapshot');
};
