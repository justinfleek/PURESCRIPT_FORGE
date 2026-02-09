/** @type {import('tailwindcss').Config} */
module.exports = {
  content: [
    "./runtime/src/**/*.{ts,tsx}",
    "./output/react/**/*.{ts,tsx}",
  ],
  theme: {
    extend: {
      // Custom theme extensions for generated components
    },
  },
  plugins: [],
}
