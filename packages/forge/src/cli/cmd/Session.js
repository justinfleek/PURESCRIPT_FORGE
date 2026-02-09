// FFI for Forge.CLI.Cmd.Session
// 1:1 parity with opencode-dev/packages/opencode/src/cli/cmd/session.ts

import * as Session from "../../session/Session.js";
import { Log } from "../../util/Log.js";

const log = Log.create({ service: "cli.session" });

// Execute session command
export const executeFFI = (args) => async () => {
  try {
    if (args.list) {
      const result = await Session.listFFI();
      if (result.tag === "Left") {
        return result;
      }
      
      for (const session of result.value) {
        console.log(`${session.id} - ${session.title} (${new Date(session.time.created).toISOString()})`);
      }
      
      return { tag: "Right", value: undefined };
    }
    
    if (args.delete) {
      const result = await Session.remove(args.delete)();
      if (result.tag === "Left") {
        return result;
      }
      console.log(`Deleted session: ${args.delete}`);
      return { tag: "Right", value: undefined };
    }
    
    if (args.info) {
      const result = await Session.get(args.info)();
      if (result.tag === "Left") {
        return result;
      }
      if (!result.value) {
        return { tag: "Left", value: `Session not found: ${args.info}` };
      }
      console.log(JSON.stringify(result.value, null, 2));
      return { tag: "Right", value: undefined };
    }
    
    if (args.export) {
      const result = await Session.get(args.export)();
      if (result.tag === "Left") {
        return result;
      }
      if (!result.value) {
        return { tag: "Left", value: `Session not found: ${args.export}` };
      }
      
      // Export session with messages
      const messagesResult = await Session.messages({ sessionID: args.export })();
      const exported = {
        session: result.value,
        messages: messagesResult.value || [],
      };
      
      console.log(JSON.stringify(exported, null, 2));
      return { tag: "Right", value: undefined };
    }
    
    // Default: list sessions
    const result = await Session.listFFI();
    if (result.tag === "Left") {
      return result;
    }
    
    if (result.value.length === 0) {
      console.log("No sessions found");
    } else {
      for (const session of result.value) {
        console.log(`${session.id} - ${session.title}`);
      }
    }
    
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
