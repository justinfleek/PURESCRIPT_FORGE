// Auth With Actor FFI
// Wraps Actor.provide from console-core

import { Actor } from "@opencode-ai/console-core/actor.js";
import { getActor } from "./Auth.js";

export const withActorFFI = async (workspace, fn) => {
  const actor = await getActor(workspace);
  return Actor.provide(actor.type, actor.properties, fn);
};
