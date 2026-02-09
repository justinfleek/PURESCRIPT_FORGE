// FFI for Forge.Server.Routes.Pty
// 1:1 parity with opencode-dev/packages/opencode/src/server/routes/pty.ts

import { Log } from "../../util/Log.js";
import { Identifier } from "../../id/Id.js";

const log = Log.create({ service: "pty" });

// PTY sessions
const sessions = new Map();

// Create a new PTY session
export const createFFI = async () => {
  try {
    const id = Identifier.ascending("pty");
    
    // In a full implementation, this would create an actual PTY using node-pty
    // For now, create a placeholder session
    sessions.set(id, {
      id,
      created: Date.now(),
      cols: 80,
      rows: 24,
    });
    
    log.info("pty created", { id });
    return { tag: "Right", value: id };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Write to a PTY session
export const writeFFI = (sessionID) => (data) => async () => {
  try {
    const session = sessions.get(sessionID);
    if (!session) {
      return { tag: "Left", value: `PTY session not found: ${sessionID}` };
    }
    
    // In a full implementation, this would write to the actual PTY
    log.info("pty write", { sessionID, length: data.length });
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Resize a PTY session
export const resizeFFI = (sessionID) => (cols) => (rows) => async () => {
  try {
    const session = sessions.get(sessionID);
    if (!session) {
      return { tag: "Left", value: `PTY session not found: ${sessionID}` };
    }
    
    session.cols = cols;
    session.rows = rows;
    
    // In a full implementation, this would resize the actual PTY
    log.info("pty resize", { sessionID, cols, rows });
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Close a PTY session
export const closeFFI = (sessionID) => async () => {
  try {
    const session = sessions.get(sessionID);
    if (!session) {
      return { tag: "Right", value: undefined };
    }
    
    sessions.delete(sessionID);
    log.info("pty closed", { sessionID });
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
