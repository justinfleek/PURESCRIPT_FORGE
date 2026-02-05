// Byte Counting Utilities FFI
// UTF-8 byte counting for accurate token usage tracking
// Single-byte precision enables accurate billing beyond token-level granularity

// Count UTF-8 bytes in a string
// Uses TextEncoder for accurate UTF-8 encoding byte counting
export function countBytes(text) {
  if (typeof text !== "string") {
    return 0;
  }
  
  try {
    // Use TextEncoder for accurate UTF-8 byte counting
    const encoder = new TextEncoder();
    const encoded = encoder.encode(text);
    return encoded.length;
  } catch (e) {
    // Fallback: approximate using string length (not accurate for multi-byte characters)
    // Fallback for environments where TextEncoder is unavailable
    return text.length;
  }
}
