// Auth Status Route FFI
// Wraps SolidJS Start route handler

import { useAuthSession } from "../context/AuthSession.js";

export const handleAuthStatus = async (event) => {
  const session = await useAuthSession();
  return Response.json(session.data);
};
