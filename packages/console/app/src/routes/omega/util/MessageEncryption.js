// Message Encryption FFI
// End-to-End Encryption for Total Privacy
// Uses Web Crypto API for AES-256-GCM encryption

// PBKDF2 iterations (high for security)
const PBKDF2_ITERATIONS = 100000;

// AES key size (256 bits = 32 bytes)
const AES_KEY_SIZE = 32;

// GCM nonce size (96 bits = 12 bytes)
const GCM_NONCE_SIZE = 12;

// Salt size (128 bits = 16 bytes)
const SALT_SIZE = 16;

// Auth tag size (128 bits = 16 bytes)
const AUTH_TAG_SIZE = 16;

// Encrypt message content using AES-256-GCM
// Returns encrypted message with nonce and salt
// PureScript Aff wrapper for async operations
export function encryptMessageImpl(plaintext, sessionKey) {
  return Promise.resolve(encryptMessageAsync(plaintext, sessionKey));
}

async function encryptMessageAsync(plaintext, sessionKey) {
  if (typeof plaintext !== "string" || typeof sessionKey !== "string") {
    throw new Error("Invalid arguments: plaintext and sessionKey must be strings");
  }

  try {
    // Generate random salt and nonce
    const salt = crypto.getRandomValues(new Uint8Array(SALT_SIZE));
    const nonce = crypto.getRandomValues(new Uint8Array(GCM_NONCE_SIZE));

    // Import session key as CryptoKey for PBKDF2
    const keyMaterial = await crypto.subtle.importKey(
      "raw",
      new TextEncoder().encode(sessionKey),
      "PBKDF2",
      false,
      ["deriveBits", "deriveKey"]
    );

    // Derive encryption key using PBKDF2
    const derivedKey = await crypto.subtle.deriveKey(
      {
        name: "PBKDF2",
        salt: salt,
        iterations: PBKDF2_ITERATIONS,
        hash: "SHA-256",
      },
      keyMaterial,
      {
        name: "AES-GCM",
        length: AES_KEY_SIZE * 8, // 256 bits
      },
      false,
      ["encrypt"]
    );

    // Encrypt plaintext
    const plaintextBytes = new TextEncoder().encode(plaintext);
    const encryptedData = await crypto.subtle.encrypt(
      {
        name: "AES-GCM",
        iv: nonce,
        tagLength: AUTH_TAG_SIZE * 8, // 128 bits
      },
      derivedKey,
      plaintextBytes
    );

    // Convert binary data to hex encoding
    const encryptedArray = new Uint8Array(encryptedData);
    const encryptedHex = Array.from(encryptedArray).map(b => b.toString(16).padStart(2, '0')).join('');
    const nonceHex = Array.from(nonce).map(b => b.toString(16).padStart(2, '0')).join('');
    const saltHex = Array.from(salt).map(b => b.toString(16).padStart(2, '0')).join('');

    return {
      encryptedContent: encryptedHex,
      nonce: nonceHex,
      salt: saltHex,
    };
  } catch (error) {
    throw new Error(`Encryption failed: ${error.message}`);
  }
}

// Decrypt message content using AES-256-GCM
// Verifies authentication tag before returning plaintext
// PureScript Aff wrapper for async operations
export function decryptMessageImpl(encrypted, sessionKey) {
  return Promise.resolve(decryptMessageAsync(encrypted, sessionKey));
}

async function decryptMessageAsync(encrypted, sessionKey) {
  if (typeof encrypted !== "object" || encrypted === null) {
    return null;
  }

  if (
    typeof encrypted.encryptedContent !== "string" ||
    typeof encrypted.nonce !== "string" ||
    typeof encrypted.salt !== "string" ||
    typeof sessionKey !== "string"
  ) {
    return null;
  }

  try {
    // Decode hex-encoded binary data
    const encryptedHex = encrypted.encryptedContent;
    const nonceHex = encrypted.nonce;
    const saltHex = encrypted.salt;

    // Convert hex strings to Uint8Array
    // Normalize odd-length hex strings by prepending zero
    const hexToBytes = (hex) => {
      const normalized = hex.length % 2 === 0 ? hex : '0' + hex;
      const matches = normalized.match(/.{1,2}/g);
      if (!matches) return new Uint8Array(0);
      return new Uint8Array(matches.map(byte => parseInt(byte, 16)));
    };
    
    const encryptedArray = hexToBytes(encryptedHex);
    const nonce = hexToBytes(nonceHex);
    const salt = hexToBytes(saltHex);

    // Import session key for PBKDF2
    const keyMaterial = await crypto.subtle.importKey(
      "raw",
      new TextEncoder().encode(sessionKey),
      "PBKDF2",
      false,
      ["deriveBits", "deriveKey"]
    );

    // Derive encryption key (same as encryption)
    const derivedKey = await crypto.subtle.deriveKey(
      {
        name: "PBKDF2",
        salt: salt,
        iterations: PBKDF2_ITERATIONS,
        hash: "SHA-256",
      },
      keyMaterial,
      {
        name: "AES-GCM",
        length: AES_KEY_SIZE * 8,
      },
      false,
      ["decrypt"]
    );

    // Decrypt
    const decryptedData = await crypto.subtle.decrypt(
      {
        name: "AES-GCM",
        iv: nonce,
        tagLength: AUTH_TAG_SIZE * 8,
      },
      derivedKey,
      encryptedArray
    );

    // Convert to string
    const plaintext = new TextDecoder().decode(decryptedData);
    return plaintext;
  } catch (error) {
    // Decryption failed (authentication tag mismatch or other error)
    return null;
  }
}

// Derive session encryption key from session ID and user secret
// Uses PBKDF2 for secure key derivation
// PureScript Aff wrapper for async operations
export function deriveSessionKeyImpl(sessionId, userSecret) {
  return Promise.resolve(deriveSessionKeyAsync(sessionId, userSecret));
}

async function deriveSessionKeyAsync(sessionId, userSecret) {
  if (typeof sessionId !== "string" || typeof userSecret !== "string") {
    throw new Error("Invalid arguments: sessionId and userSecret must be strings");
  }

  try {
    // Use session ID as salt for key derivation
    const salt = new TextEncoder().encode(sessionId);

    // Import user secret as key material
    const keyMaterial = await crypto.subtle.importKey(
      "raw",
      new TextEncoder().encode(userSecret),
      "PBKDF2",
      false,
      ["deriveBits"]
    );

    // Derive 256-bit key
    const derivedBits = await crypto.subtle.deriveBits(
      {
        name: "PBKDF2",
        salt: salt,
        iterations: PBKDF2_ITERATIONS,
        hash: "SHA-256",
      },
      keyMaterial,
      AES_KEY_SIZE * 8 // 256 bits
    );

    // Convert derived key to hex encoding for storage/transmission
    const derivedArray = new Uint8Array(derivedBits);
    return Array.from(derivedArray).map(b => b.toString(16).padStart(2, '0')).join('');
  } catch (error) {
    throw new Error(`Key derivation failed: ${error.message}`);
  }
}
