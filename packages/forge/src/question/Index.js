// FFI for Forge.Question.Index
// 1:1 parity with opencode-dev/packages/opencode/src/question/index.ts

import { Bus } from "../bus/Index.js";
import { BusEvent } from "../bus/BusEvent.js";
import { Identifier } from "../id/Id.js";
import { Instance } from "../project/Instance.js";
import { Log } from "../util/Log.js";

const log = Log.create({ service: "question" });

export const Event = {
  Asked: BusEvent.define("question.asked", {
    id: "string",
    sessionID: "string",
    questions: "array",
    tool: "object",
  }),
  Replied: BusEvent.define("question.replied", {
    sessionID: "string",
    requestID: "string",
    answers: "array",
  }),
  Rejected: BusEvent.define("question.rejected", {
    sessionID: "string",
    requestID: "string",
  }),
};

const state = Instance.state(async () => ({
  pending: {},
}));

export const ask = (input) => async () => {
  const s = await state();
  const id = Identifier.ascending("question");

  log.info("asking", { id, questions: input.questions.length });

  return new Promise((resolve, reject) => {
    const info = {
      id,
      sessionID: input.sessionID,
      questions: input.questions,
      tool: input.tool,
    };
    s.pending[id] = {
      info,
      resolve,
      reject,
    };
    Bus.publish(Event.Asked, info);
  });
};

export const reply = (input) => async () => {
  const s = await state();
  const existing = s.pending[input.requestID];
  if (!existing) {
    log.warn("reply for unknown request", { requestID: input.requestID });
    return;
  }
  delete s.pending[input.requestID];

  log.info("replied", { requestID: input.requestID, answers: input.answers });

  Bus.publish(Event.Replied, {
    sessionID: existing.info.sessionID,
    requestID: existing.info.id,
    answers: input.answers,
  });

  existing.resolve(input.answers);
};

export const reject = (requestID) => async () => {
  const s = await state();
  const existing = s.pending[requestID];
  if (!existing) {
    log.warn("reject for unknown request", { requestID });
    return;
  }
  delete s.pending[requestID];

  log.info("rejected", { requestID });

  Bus.publish(Event.Rejected, {
    sessionID: existing.info.sessionID,
    requestID: existing.info.id,
  });

  existing.reject(new RejectedError());
};

export class RejectedError extends Error {
  constructor() {
    super("The user dismissed this question");
  }
}

export const list = async () => {
  const s = await state();
  return Object.values(s.pending).map((x) => x.info);
};
