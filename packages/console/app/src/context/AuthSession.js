// Auth Session FFI
// Wraps SolidJS Start's useAuthSession

import { useSession } from "@solidjs/start/http";
import { Resource } from "@opencode-ai/console-resource";

export const useAuthSession = async () => {
  const session = useSession({
    password: Resource.OMEGA_SESSION_SECRET.value,
    name: "auth",
    maxAge: 60 * 60 * 24 * 365,
    cookie: {
      secure: false,
      httpOnly: true,
    },
  });
  return {
    data: session.data,
    update: async (fn) => {
      await session.update(fn);
    },
  };
};
