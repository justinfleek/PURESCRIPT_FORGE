// FFI for Forge.Server.Routes.Question
// 1:1 parity with opencode-dev/packages/opencode/src/server/routes/question.ts

import { Bus } from "../../bus/Index.js";
import { Log } from "../../util/Log.js";

const log = Log.create({ service: "question" });

// Question answer events
export const Event = {
  Answer: {
    type: "question.answer",
  },
};

// Answer a question
export const answerFFI = (sessionID) => (questionID) => (answer) => async () => {
  try {
    log.info("question answered", { sessionID, questionID, answer });
    
    Bus.publish(Event.Answer.type, {
      sessionID,
      questionID,
      answer,
    });
    
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// List pending questions for a session
export const pendingFFI = (sessionID) => async () => {
  try {
    // In a full implementation, this would track pending questions
    // For now, return empty array
    return { tag: "Right", value: [] };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
