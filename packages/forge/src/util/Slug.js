// FFI for Forge.Util.Slug
// 1:1 parity with @opencode-ai/util/slug

// Adjectives for slug generation
const adjectives = [
  "autumn", "hidden", "bitter", "misty", "silent", "empty", "dry", "dark",
  "summer", "icy", "delicate", "quiet", "white", "cool", "spring", "winter",
  "patient", "twilight", "dawn", "crimson", "wispy", "weathered", "blue",
  "billowing", "broken", "cold", "damp", "falling", "frosty", "green",
  "long", "late", "lingering", "bold", "little", "morning", "muddy", "old",
  "red", "rough", "still", "small", "sparkling", "throbbing", "shy",
  "wandering", "withered", "wild", "black", "young", "holy", "solitary",
  "fragrant", "aged", "snowy", "proud", "floral", "restless", "divine",
  "polished", "ancient", "purple", "lively", "nameless"
];

// Nouns for slug generation
const nouns = [
  "waterfall", "river", "breeze", "moon", "rain", "wind", "sea", "morning",
  "snow", "lake", "sunset", "pine", "shadow", "leaf", "dawn", "glitter",
  "forest", "hill", "cloud", "meadow", "sun", "glade", "bird", "brook",
  "butterfly", "bush", "dew", "dust", "field", "fire", "flower", "firefly",
  "feather", "grass", "haze", "mountain", "night", "pond", "darkness",
  "snowflake", "silence", "sound", "sky", "shape", "surf", "thunder",
  "violet", "water", "wildflower", "wave", "water", "resonance", "sun",
  "wood", "dream", "cherry", "tree", "fog", "frost", "voice", "paper",
  "frog", "smoke", "star"
];

// Generate a random slug
export const create = () => {
  const adj = adjectives[Math.floor(Math.random() * adjectives.length)];
  const noun = nouns[Math.floor(Math.random() * nouns.length)];
  const num = Math.floor(Math.random() * 1000);
  return `${adj}-${noun}-${num}`;
};

// Validate a slug
export const isValid = (slug) => {
  return /^[a-z]+-[a-z]+-\d+$/.test(slug);
};

// Parse a slug into parts
export const parse = (slug) => {
  const parts = slug.split("-");
  if (parts.length !== 3) return null;
  return {
    adjective: parts[0],
    noun: parts[1],
    number: parseInt(parts[2], 10)
  };
};

// Namespace for direct JS usage (internal - not exported to avoid PS FFI issues)
const SlugNamespace = {
  create,
  isValid,
  parse
};

// Note: The Slug namespace is available for JS consumers via:
// import { create, isValid, parse } from "./Slug.js"
// The uppercase "Slug" export has been removed to fix PS FFI compilation
