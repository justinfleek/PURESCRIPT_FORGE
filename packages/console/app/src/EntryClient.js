// Entry Client FFI
// Wraps SolidJS Start client mount

import { mount, StartClient } from "@solidjs/start/client";

export const mountClient = () => {
  const appElement = document.getElementById("app");
  if (appElement === null) {
    throw new Error("App element not found");
  }
  mount(() => <StartClient />, appElement);
};
