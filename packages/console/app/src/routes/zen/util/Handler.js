// Omega Handler FFI
// Wraps the main omega handler from TypeScript

import { handler } from "./handler.js";

export const handleOmegaRequest = async (event, options) => {
  return handler(event, options);
};
