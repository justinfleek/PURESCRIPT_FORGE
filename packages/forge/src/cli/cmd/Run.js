// FFI for Forge.CLI.Cmd.Run
// 1:1 parity with opencode-dev/packages/opencode/src/cli/cmd/run.ts

import { Log } from "../../util/Log.js";
import * as Session from "../../session/Session.js";
import { SessionPrompt } from "../../session/Prompt.js";
import { Provider } from "../../provider/Provider.js";

const log = Log.create({ service: "cli.run" });

// Execute the run command
export const executeFFI = (args) => async () => {
  try {
    log.info("run command", { args });

    // Get or create session
    let sessionID = args.session;
    let sessionInfo;

    if (args.continue && sessionID) {
      // Continue existing session
      const result = await Session.get(sessionID)();
      if (result.tag === "Left" || !result.value) {
        return { tag: "Left", value: `Session not found: ${sessionID}` };
      }
      sessionInfo = result.value;
    } else {
      // Create new session
      const createResult = await Session.create({
        title: args.title,
        permission: null,
      })();
      if (createResult.tag === "Left") {
        return { tag: "Left", value: createResult.value };
      }
      sessionInfo = createResult.value;
      sessionID = sessionInfo.id;
    }

    // Get model
    let model = null;
    if (args.model) {
      const parsed = Provider.parseModel(args.model);
      model = {
        providerID: parsed.providerID,
        modelID: parsed.modelID,
      };
    } else {
      try {
        model = await Provider.defaultModel();
      } catch (e) {
        return { tag: "Left", value: "No model specified and no default model available" };
      }
    }

    // Build prompt parts
    const parts = [];

    // Add message parts
    if (args.message && args.message.length > 0) {
      const text = args.message.join(" ");
      parts.push({ type: "text", text });
    }

    // Add file attachments
    if (args.file && args.file.length > 0) {
      for (const filePath of args.file) {
        parts.push({
          type: "file",
          path: filePath,
        });
      }
    }

    if (parts.length === 0) {
      return { tag: "Left", value: "No message or files provided" };
    }

    // Send prompt
    const promptResult = await SessionPrompt.prompt({
      sessionID,
      model,
      agent: args.agent,
      parts,
      variant: args.variant,
    });

    // Handle output format
    if (args.format === "json") {
      log.info("session result", { sessionID, info: promptResult.info });
    } else {
      console.log(`Session: ${sessionID}`);
      console.log(`Message: ${promptResult.info.id}`);
    }

    // Share if requested
    if (args.share) {
      await Session.share(sessionID)().catch((e) => {
        log.warn("failed to share session", { error: e.message });
      });
    }

    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
