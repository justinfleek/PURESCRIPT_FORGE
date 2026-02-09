// FFI for Forge.PTY.Index
// 1:1 parity with opencode-dev/packages/opencode/src/pty/index.ts

import { BusEvent } from "../bus/BusEvent.js";
import { Bus } from "../bus/Index.js";
import { Identifier } from "../id/Id.js";
import { Log } from "../util/Log.js";
import { Instance } from "../project/Instance.js";
import { lazy } from "../util/Lazy.js";
import { Shell } from "../shell/Shell.js";

const log = Log.create({ service: "pty" });

const BUFFER_LIMIT = 1024 * 1024 * 2;
const BUFFER_CHUNK = 64 * 1024;

const pty = lazy(async () => {
  const { spawn } = await import("bun-pty");
  return spawn;
});

export const Event = {
  Created: BusEvent.define("pty.created", { info: "object" }),
  Updated: BusEvent.define("pty.updated", { info: "object" }),
  Exited: BusEvent.define("pty.exited", { id: "string", exitCode: "number" }),
  Deleted: BusEvent.define("pty.deleted", { id: "string" }),
};

const state = Instance.state(
  () => new Map(),
  async (sessions) => {
    for (const session of sessions.values()) {
      try {
        session.process.kill();
      } catch {}
      for (const ws of session.subscribers) {
        ws.close();
      }
    }
    sessions.clear();
  },
);

export const list = () => Array.from(state().values()).map((s) => s.info);

export const get = (id) => () => state().get(id)?.info || null;

export const create = (input) => async () => {
  const id = Identifier.create("pty", false);
  const command = input.command || Shell.preferred();
  const args = input.args || [];
  if (command.endsWith("sh")) {
    args.push("-l");
  }

  const cwd = input.cwd || Instance.directory;
  const env = {
    ...process.env,
    ...input.env,
    TERM: "xterm-256color",
    FORGE_TERMINAL: "1",
  };
  log.info("creating session", { id, cmd: command, args, cwd });

  const spawn = await pty();
  const ptyProcess = spawn(command, args, {
    name: "xterm-256color",
    cwd,
    env,
  });

  const info = {
    id,
    title: input.title || `Terminal ${id.slice(-4)}`,
    command,
    args,
    cwd,
    status: "running",
    pid: ptyProcess.pid,
  };
  const session = {
    info,
    process: ptyProcess,
    buffer: "",
    subscribers: new Set(),
  };
  state().set(id, session);
  
  ptyProcess.onData((data) => {
    let open = false;
    for (const ws of session.subscribers) {
      if (ws.readyState !== 1) {
        session.subscribers.delete(ws);
        continue;
      }
      open = true;
      ws.send(data);
    }
    if (open) return;
    session.buffer += data;
    if (session.buffer.length <= BUFFER_LIMIT) return;
    session.buffer = session.buffer.slice(-BUFFER_LIMIT);
  });
  
  ptyProcess.onExit(({ exitCode }) => {
    log.info("session exited", { id, exitCode });
    session.info.status = "exited";
    for (const ws of session.subscribers) {
      ws.close();
    }
    session.subscribers.clear();
    Bus.publish(Event.Exited, { id, exitCode });
    state().delete(id);
  });
  
  Bus.publish(Event.Created, { info });
  return info;
};

export const update = (id) => (input) => async () => {
  const session = state().get(id);
  if (!session) return null;
  if (input.title) {
    session.info.title = input.title;
  }
  if (input.size) {
    session.process.resize(input.size.cols, input.size.rows);
  }
  Bus.publish(Event.Updated, { info: session.info });
  return session.info;
};

export const remove = (id) => async () => {
  const session = state().get(id);
  if (!session) return;
  log.info("removing session", { id });
  try {
    session.process.kill();
  } catch {}
  for (const ws of session.subscribers) {
    ws.close();
  }
  state().delete(id);
  Bus.publish(Event.Deleted, { id });
};

export const resize = (id) => (cols) => (rows) => () => {
  const session = state().get(id);
  if (session && session.info.status === "running") {
    session.process.resize(cols, rows);
  }
};

export const write = (id) => (data) => () => {
  const session = state().get(id);
  if (session && session.info.status === "running") {
    session.process.write(data);
  }
};

export const connect = (id) => (ws) => () => {
  const session = state().get(id);
  if (!session) {
    ws.close();
    return null;
  }
  log.info("client connected to session", { id });
  session.subscribers.add(ws);
  if (session.buffer) {
    const buffer = session.buffer.length <= BUFFER_LIMIT ? session.buffer : session.buffer.slice(-BUFFER_LIMIT);
    session.buffer = "";
    try {
      for (let i = 0; i < buffer.length; i += BUFFER_CHUNK) {
        ws.send(buffer.slice(i, i + BUFFER_CHUNK));
      }
    } catch {
      session.subscribers.delete(ws);
      session.buffer = buffer;
      ws.close();
      return null;
    }
  }
  return {
    onMessage: (message) => {
      session.process.write(String(message));
    },
    onClose: () => {
      log.info("client disconnected from session", { id });
      session.subscribers.delete(ws);
    },
  };
};
