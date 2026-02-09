// Forge.Id.Id FFI - Unique ID generation
// 1:1 parity with opencode-dev/packages/opencode/src/id/id.ts

import { randomUUID } from "crypto";
import { ulid, decodeTime } from "ulid";

// URL-safe alphabet for nanoid-style IDs
const ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_-";

// Generate UUID v4
export const generateUUIDFFI = () => {
  return randomUUID();
};

// Generate nanoid-style short ID
export const generateNanoidFFI = (size) => () => {
  let id = "";
  const randomBytes = new Uint8Array(size);
  crypto.getRandomValues(randomBytes);
  
  for (let i = 0; i < size; i++) {
    id += ALPHABET[randomBytes[i] % ALPHABET.length];
  }
  
  return id;
};

// Check if all characters match predicate
export const stringAllImpl = (pred) => (codePoints) => {
  for (const cp of codePoints) {
    const char = String.fromCodePoint(cp);
    if (!pred(char)) {
      return false;
    }
  }
  return true;
};

// ============================================================================
// Identifier namespace (matches opencode-original)
// ============================================================================

// Invert a ULID for descending sort order
function invertUlid(id) {
  const chars = "0123456789ABCDEFGHJKMNPQRSTVWXYZ";
  let result = "";
  for (let i = 0; i < id.length; i++) {
    const char = id[i].toUpperCase();
    const index = chars.indexOf(char);
    if (index >= 0) {
      result += chars[31 - index];
    } else {
      result += char;
    }
  }
  return result;
}

// Generate ascending ID (normal ULID)
export function ascending(prefix, id) {
  const base = id ?? ulid();
  return prefix + "_" + base;
}

// Generate descending ID (inverted ULID for reverse chronological sort)
export function descending(prefix, id) {
  const base = id ?? ulid();
  return prefix + "_" + invertUlid(base);
}

// Extract timestamp from ID
export function timestamp(id) {
  const parts = id.split("_");
  if (parts.length < 2) return null;
  try {
    const base = parts[1];
    // Try to decode as normal ULID first
    return decodeTime(base);
  } catch {
    try {
      // Try as inverted ULID
      return decodeTime(invertUlid(parts[1]));
    } catch {
      return null;
    }
  }
}

// Schema for validating identifier format
export function schema(prefix) {
  const pattern = new RegExp(`^${prefix}_[0-9A-Z]{26}$`, "i");
  return {
    validate: (value) => pattern.test(value),
    prefix,
  };
}

// Identifier namespace export for direct usage
export const Identifier = {
  ascending,
  descending,
  timestamp,
  schema,
};
