// Middleware FFI
// Wraps SolidJS Start middleware creation

import { createMiddleware as createSolidMiddleware } from "@solidjs/start/middleware";

export const createMiddleware = () => {
  return createSolidMiddleware({
    onBeforeResponse() {},
  });
};
