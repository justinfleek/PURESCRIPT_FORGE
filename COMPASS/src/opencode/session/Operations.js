// FFI for Opencode.Session.Operations
// Provides time utilities and other native functions

"use strict";

// Get current time in milliseconds
export const nowMillis = () => Date.now();

// Unsafe coerce (identity at runtime)
export const unsafeCoerce = (x) => x;
