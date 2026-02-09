// FFI for Forge.Util.Log
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/log.ts

import path from "path";
import fs from "fs/promises";
import { Global } from "../global/Index.js";

const Level = {
  DEBUG: "DEBUG",
  INFO: "INFO",
  WARN: "WARN",
  ERROR: "ERROR"
};

const levelPriority = {
  DEBUG: 0,
  INFO: 1,
  WARN: 2,
  ERROR: 3,
};

let level = "INFO";

function shouldLog(input) {
  return levelPriority[input] >= levelPriority[level];
}

const loggers = new Map();

let logpath = "";

export const file = () => logpath;

let write = (msg) => {
  process.stderr.write(msg);
  return msg.length;
};

async function cleanup(dir) {
  try {
    const glob = new Bun.Glob("????-??-??T??????.log");
    const files = await Array.fromAsync(
      glob.scan({
        cwd: dir,
        absolute: true,
      })
    );
    if (files.length <= 5) return;

    const filesToDelete = files.slice(0, -10);
    await Promise.all(filesToDelete.map((file) => fs.unlink(file).catch(() => {})));
  } catch {
    // Ignore cleanup errors
  }
}

function formatError(error, depth = 0) {
  const result = error.message;
  return error.cause instanceof Error && depth < 10
    ? result + " Caused by: " + formatError(error.cause, depth + 1)
    : result;
}

let last = Date.now();

export const init = (options) => () => {
  return new Promise(async (resolve) => {
    if (options.level) level = options.level;
    cleanup(Global.Path.log);
    if (options.print) {
      resolve();
      return;
    }
    logpath = path.join(
      Global.Path.log,
      options.dev ? "dev.log" : new Date().toISOString().split(".")[0].replace(/:/g, "") + ".log"
    );
    const logfile = Bun.file(logpath);
    await fs.truncate(logpath).catch(() => {});
    const writer = logfile.writer();
    write = async (msg) => {
      const num = writer.write(msg);
      writer.flush();
      return num;
    };
    resolve();
  });
};

export const create = (tags) => {
  tags = tags || {};

  const service = tags["service"];
  if (service && typeof service === "string") {
    const cached = loggers.get(service);
    if (cached) {
      return cached;
    }
  }

  function build(message, extra) {
    const prefix = Object.entries({
      ...tags,
      ...extra,
    })
      .filter(([_, value]) => value !== undefined && value !== null)
      .map(([key, value]) => {
        const prefix = `${key}=`;
        if (value instanceof Error) return prefix + formatError(value);
        if (typeof value === "object") return prefix + JSON.stringify(value);
        return prefix + value;
      })
      .join(" ");
    const next = new Date();
    const diff = next.getTime() - last;
    last = next.getTime();
    return [next.toISOString().split(".")[0], "+" + diff + "ms", prefix, message].filter(Boolean).join(" ") + "\n";
  }

  const result = {
    debug: (message) => (extra) => () => {
      if (shouldLog("DEBUG")) {
        write("DEBUG " + build(message, extra));
      }
    },
    info: (message) => (extra) => () => {
      if (shouldLog("INFO")) {
        write("INFO  " + build(message, extra));
      }
    },
    error: (message) => (extra) => () => {
      if (shouldLog("ERROR")) {
        write("ERROR " + build(message, extra));
      }
    },
    warn: (message) => (extra) => () => {
      if (shouldLog("WARN")) {
        write("WARN  " + build(message, extra));
      }
    },
    tag: (key) => (value) => {
      if (tags) tags[key] = value;
      return result;
    },
    clone: () => create({ ...tags }),
    time: (message) => (extra) => () => {
      const now = Date.now();
      result.info(message)({ status: "started", ...extra })();
      function stop() {
        result.info(message)({
          status: "completed",
          duration: Date.now() - now,
          ...extra,
        })();
      }
      return {
        stop: () => stop,
      };
    },
  };

  if (service && typeof service === "string") {
    loggers.set(service, result);
  }

  return result;
};

export const defaultLogger = create({ service: "default" });

// Log namespace for JS consumers (non-curried versions)
export const Log = {
  create: (tags) => {
    const logger = create(tags);
    return {
      debug: (message, extra) => logger.debug(message)(extra || {})(),
      info: (message, extra) => logger.info(message)(extra || {})(),
      warn: (message, extra) => logger.warn(message)(extra || {})(),
      error: (message, extra) => logger.error(message)(extra || {})(),
      tag: (key, value) => logger.tag(key)(value),
      clone: () => logger.clone(),
      time: (message, extra) => {
        const timer = logger.time(message)(extra || {})();
        return {
          stop: () => timer.stop()(),
          [Symbol.dispose]: () => timer.stop()(),
        };
      },
    };
  },
  file,
  init,
};
