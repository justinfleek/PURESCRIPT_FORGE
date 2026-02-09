// FFI for Forge.Session.Summary
// 1:1 parity with opencode-dev/packages/opencode/src/session/summary.ts

import { Provider } from "../provider/Provider.js";
import { fn } from "../util/Fn.js";
import { Session } from "./Index.js";
import { MessageV2 } from "./MessageV2.js";
import { Identifier } from "../id/Id.js";
import { Snapshot } from "../snapshot/Index.js";
import { Log } from "../util/Log.js";
import path from "path";
import { Instance } from "../project/Instance.js";
import { Storage } from "../storage/Storage.js";
import { Bus } from "../bus/Index.js";
import { LLM } from "./LLM.js";
import { Agent } from "../agent/Agent.js";

const log = Log.create({ service: "session.summary" });

function unquoteGitPath(input) {
  if (!input.startsWith('"')) return input;
  if (!input.endsWith('"')) return input;
  const body = input.slice(1, -1);
  const bytes = [];

  for (let i = 0; i < body.length; i++) {
    const char = body[i];
    if (char !== "\\") {
      bytes.push(char.charCodeAt(0));
      continue;
    }

    const next = body[i + 1];
    if (!next) {
      bytes.push("\\".charCodeAt(0));
      continue;
    }

    if (next >= "0" && next <= "7") {
      const chunk = body.slice(i + 1, i + 4);
      const match = chunk.match(/^[0-7]{1,3}/);
      if (!match) {
        bytes.push(next.charCodeAt(0));
        i++;
        continue;
      }
      bytes.push(parseInt(match[0], 8));
      i += match[0].length;
      continue;
    }

    const escaped =
      next === "n" ? "\n" :
      next === "r" ? "\r" :
      next === "t" ? "\t" :
      next === "b" ? "\b" :
      next === "f" ? "\f" :
      next === "v" ? "\v" :
      next === "\\" || next === '"' ? next :
      undefined;

    bytes.push((escaped ?? next).charCodeAt(0));
    i++;
  }

  return Buffer.from(bytes).toString();
}

export const summarize = (input) => async () => {
  const all = await Session.messages({ sessionID: input.sessionID });
  await Promise.all([
    summarizeSession({ sessionID: input.sessionID, messages: all }),
    summarizeMessage({ messageID: input.messageID, messages: all }),
  ]);
};

async function summarizeSession(input) {
  const files = new Set(
    input.messages
      .flatMap((x) => x.parts)
      .filter((x) => x.type === "patch")
      .flatMap((x) => x.files)
      .map((x) => path.relative(Instance.worktree, x).replaceAll("\\", "/")),
  );
  const diffs = await computeDiff({ messages: input.messages })().then((x) =>
    x.filter((x) => files.has(x.file)),
  );
  await Session.update(input.sessionID, (draft) => {
    draft.summary = {
      additions: diffs.reduce((sum, x) => sum + x.additions, 0),
      deletions: diffs.reduce((sum, x) => sum + x.deletions, 0),
      files: diffs.length,
    };
  });
  await Storage.write(["session_diff", input.sessionID], diffs);
  Bus.publish(Session.Event.Diff, {
    sessionID: input.sessionID,
    diff: diffs,
  });
}

async function summarizeMessage(input) {
  const messages = input.messages.filter(
    (m) => m.info.id === input.messageID || (m.info.role === "assistant" && m.info.parentID === input.messageID),
  );
  const msgWithParts = messages.find((m) => m.info.id === input.messageID);
  const userMsg = msgWithParts.info;
  const diffs = await computeDiff({ messages })();
  userMsg.summary = {
    ...userMsg.summary,
    diffs,
  };
  await Session.updateMessage(userMsg);

  const textPart = msgWithParts.parts.find((p) => p.type === "text" && !p.synthetic);
  if (textPart && !userMsg.summary?.title) {
    const agent = await Agent.get("title");
    if (!agent) return;
    const stream = await LLM.stream({
      agent,
      user: userMsg,
      tools: {},
      model: agent.model
        ? await Provider.getModel(agent.model.providerID, agent.model.modelID)
        : ((await Provider.getSmallModel(userMsg.model.providerID)) ??
          (await Provider.getModel(userMsg.model.providerID, userMsg.model.modelID))),
      small: true,
      messages: [
        {
          role: "user",
          content: `
            The following is the text to summarize:
            <text>
            ${textPart?.text ?? ""}
            </text>
          `,
        },
      ],
      abort: new AbortController().signal,
      sessionID: userMsg.sessionID,
      system: [],
      retries: 3,
    })();
    const result = await stream.text;
    log.info("title", { title: result });
    userMsg.summary.title = result;
    await Session.updateMessage(userMsg);
  }
}

export const diff = (input) => async () => {
  const diffs = await Storage.read(["session_diff", input.sessionID]).catch(() => []);
  const next = diffs.map((item) => {
    const file = unquoteGitPath(item.file);
    if (file === item.file) return item;
    return { ...item, file };
  });
  const changed = next.some((item, i) => item.file !== diffs[i]?.file);
  if (changed) Storage.write(["session_diff", input.sessionID], next).catch(() => {});
  return next;
};

export const computeDiff = (input) => async () => {
  let from;
  let to;

  for (const item of input.messages) {
    if (!from) {
      for (const part of item.parts) {
        if (part.type === "step-start" && part.snapshot) {
          from = part.snapshot;
          break;
        }
      }
    }

    for (const part of item.parts) {
      if (part.type === "step-finish" && part.snapshot) {
        to = part.snapshot;
        break;
      }
    }
  }

  if (from && to) return Snapshot.diffFull(from, to);
  return [];
};
