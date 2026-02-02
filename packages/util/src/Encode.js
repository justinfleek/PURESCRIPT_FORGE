// FFI for Encode.purs
export const base64Encode = (value) => {
  const bytes = new TextEncoder().encode(value);
  const binary = Array.from(bytes, (b) => String.fromCharCode(b)).join("");
  return btoa(binary).replace(/\+/g, "-").replace(/\//g, "_").replace(/=/g, "");
};

export const base64Decode = (value) => {
  const binary = atob(value.replace(/-/g, "+").replace(/_/g, "/"));
  const bytes = Uint8Array.from(binary, (c) => c.charCodeAt(0));
  return new TextDecoder().decode(bytes);
};

export const toBase36 = (n) => (n >>> 0).toString(36);
