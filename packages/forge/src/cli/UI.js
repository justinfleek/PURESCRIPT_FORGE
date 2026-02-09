// Forge.CLI.UI FFI

import * as readline from 'readline';

// Print line to stdout
export const printlnFFI = (str) => () => {
  console.log(str);
};

// Print without newline
export const printFFI = (str) => () => {
  process.stdout.write(str);
};

// Print to stderr
export const printErrorFFI = (str) => () => {
  console.error(str);
};

// Clear screen
export const clearScreenFFI = () => {
  process.stdout.write('\x1b[2J\x1b[H');
};

// Clear current line
export const clearLineFFI = () => {
  process.stdout.write('\x1b[2K\r');
};

// Move cursor
export const moveCursorFFI = (row) => (col) => () => {
  process.stdout.write(`\x1b[${row};${col}H`);
};

// Prompt for input
export const promptFFI = (question) => () => {
  return new Promise((resolve) => {
    const rl = readline.createInterface({
      input: process.stdin,
      output: process.stdout
    });
    
    rl.question(question, (answer) => {
      rl.close();
      resolve(answer);
    });
  });
};

// Number conversions
export const toNumberFFI = (n) => n;
export const floorFFI = (n) => Math.floor(n);
