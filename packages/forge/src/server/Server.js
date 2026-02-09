// FFI for Forge.Server.Server
// 1:1 parity with opencode-dev/packages/opencode/src/server/server.ts

import { BusEvent } from "../bus/BusEvent.js";
import { Bus } from "../bus/Index.js";
import { Log } from "../util/Log.js";
import { describeRoute, generateSpecs, validator, resolver, openAPIRouteHandler } from "hono-openapi";
import { Hono } from "hono";
import { cors } from "hono/cors";
import { streamSSE } from "hono/streaming";
import { proxy } from "hono/proxy";
import { basicAuth } from "hono/basic-auth";
import { Provider } from "../provider/Provider.js";
import { NamedError } from "../util/Error.js";
import { LSP } from "../lsp/Index.js";
import { Format } from "../format/Index.js";
import { TuiRoutes } from "./routes/Tui.js";
import { Instance } from "../project/Instance.js";
import { Vcs } from "../project/VCS.js";
import { Agent } from "../agent/Agent.js";
import { Skill } from "../skill/Skill.js";
import { Auth } from "../auth/Index.js";
import { Flag } from "../flag/Flag.js";
import { Command } from "../command/Index.js";
import { Global } from "../global/Index.js";
import { ProjectRoutes } from "./routes/Project.js";
import { SessionRoutes } from "./routes/Session.js";
import { PtyRoutes } from "./routes/Pty.js";
import { McpRoutes } from "./routes/Mcp.js";
import { FileRoutes } from "./routes/File.js";
import { ConfigRoutes } from "./routes/Config.js";
import { ExperimentalRoutes } from "./routes/Experimental.js";
import { ProviderRoutes } from "./routes/Provider.js";
import { lazy } from "../util/Lazy.js";
import { InstanceBootstrap } from "../project/Bootstrap.js";
import { Storage } from "../storage/Storage.js";
import { websocket } from "hono/bun";
import { HTTPException } from "hono/http-exception";
import { errors } from "./Error.js";
import { QuestionRoutes } from "./routes/Question.js";
import { PermissionRoutes } from "./routes/Permission.js";
import { GlobalRoutes } from "./routes/Global.js";
import { MDNS } from "./MDNS.js";

// Suppress AI SDK warnings
globalThis.AI_SDK_LOG_WARNINGS = false;

const log = Log.create({ service: "server" });

let _url;
let _corsWhitelist = [];

export const url = () => _url ?? new URL("http://localhost:4096");

const app = new Hono();

export const App = lazy(
  () =>
    app
      .onError((err, c) => {
        log.error("failed", { error: err });
        if (err instanceof NamedError) {
          let status;
          if (err instanceof Storage.NotFoundError) status = 404;
          else if (err instanceof Provider.ModelNotFoundError) status = 400;
          else if (err.name.startsWith("Worktree")) status = 400;
          else status = 500;
          return c.json(err.toObject(), { status });
        }
        if (err instanceof HTTPException) return err.getResponse();
        const message = err instanceof Error && err.stack ? err.stack : err.toString();
        return c.json(new NamedError.Unknown({ message }).toObject(), { status: 500 });
      })
      .use((c, next) => {
        const password = Flag.FORGE_SERVER_PASSWORD;
        if (!password) return next();
        const username = Flag.FORGE_SERVER_USERNAME ?? "forge";
        return basicAuth({ username, password })(c, next);
      })
      .use(async (c, next) => {
        const skipLogging = c.req.path === "/log";
        if (!skipLogging) {
          log.info("request", { method: c.req.method, path: c.req.path });
        }
        const timer = log.time("request", { method: c.req.method, path: c.req.path });
        await next();
        if (!skipLogging) {
          timer.stop();
        }
      })
      .use(
        cors({
          origin(input) {
            if (!input) return;
            if (input.startsWith("http://localhost:")) return input;
            if (input.startsWith("http://127.0.0.1:")) return input;
            if (input === "tauri://localhost" || input === "http://tauri.localhost") return input;
            if (/^https:\/\/([a-z0-9-]+\.)*forge\.ai$/.test(input)) return input;
            if (_corsWhitelist.includes(input)) return input;
            return;
          },
        }),
      )
      .route("/global", GlobalRoutes())
      .put(
        "/auth/:providerID",
        describeRoute({
          summary: "Set auth credentials",
          description: "Set authentication credentials",
          operationId: "auth.set",
          responses: {
            200: {
              description: "Successfully set authentication credentials",
              content: { "application/json": { schema: resolver({ type: "boolean" }) } },
            },
            ...errors(400),
          },
        }),
        validator("param", { providerID: "string" }),
        validator("json", Auth.Info),
        async (c) => {
          const providerID = c.req.valid("param").providerID;
          const info = c.req.valid("json");
          await Auth.set(providerID, info);
          return c.json(true);
        },
      )
      .delete(
        "/auth/:providerID",
        describeRoute({
          summary: "Remove auth credentials",
          description: "Remove authentication credentials",
          operationId: "auth.remove",
          responses: {
            200: {
              description: "Successfully removed authentication credentials",
              content: { "application/json": { schema: resolver({ type: "boolean" }) } },
            },
            ...errors(400),
          },
        }),
        validator("param", { providerID: "string" }),
        async (c) => {
          const providerID = c.req.valid("param").providerID;
          await Auth.remove(providerID);
          return c.json(true);
        },
      )
      .use(async (c, next) => {
        let directory = c.req.query("directory") || c.req.header("x-forge-directory") || process.cwd();
        try {
          directory = decodeURIComponent(directory);
        } catch {
          // fallback
        }
        return Instance.provide({
          directory,
          init: InstanceBootstrap,
          async fn() {
            return next();
          },
        });
      })
      .get(
        "/doc",
        openAPIRouteHandler(app, {
          documentation: {
            info: { title: "forge", version: "0.0.3", description: "forge api" },
            openapi: "3.1.1",
          },
        }),
      )
      .use(validator("query", { directory: { type: "string", optional: true } }))
      .route("/project", ProjectRoutes())
      .route("/pty", PtyRoutes())
      .route("/config", ConfigRoutes())
      .route("/experimental", ExperimentalRoutes())
      .route("/session", SessionRoutes())
      .route("/permission", PermissionRoutes())
      .route("/question", QuestionRoutes())
      .route("/provider", ProviderRoutes())
      .route("/", FileRoutes())
      .route("/mcp", McpRoutes())
      .route("/tui", TuiRoutes())
      .post(
        "/instance/dispose",
        describeRoute({
          summary: "Dispose instance",
          description: "Clean up and dispose the current Forge instance.",
          operationId: "instance.dispose",
          responses: {
            200: {
              description: "Instance disposed",
              content: { "application/json": { schema: resolver({ type: "boolean" }) } },
            },
          },
        }),
        async (c) => {
          await Instance.dispose();
          return c.json(true);
        },
      )
      .get(
        "/path",
        describeRoute({
          summary: "Get paths",
          description: "Retrieve path information for the Forge instance.",
          operationId: "path.get",
          responses: {
            200: {
              description: "Path",
              content: {
                "application/json": {
                  schema: resolver({
                    type: "object",
                    properties: {
                      home: { type: "string" },
                      state: { type: "string" },
                      config: { type: "string" },
                      worktree: { type: "string" },
                      directory: { type: "string" },
                    },
                  }),
                },
              },
            },
          },
        }),
        async (c) => {
          return c.json({
            home: Global.Path.home,
            state: Global.Path.state,
            config: Global.Path.config,
            worktree: Instance.worktree,
            directory: Instance.directory,
          });
        },
      )
      .get(
        "/vcs",
        describeRoute({
          summary: "Get VCS info",
          description: "Retrieve version control system information.",
          operationId: "vcs.get",
          responses: {
            200: {
              description: "VCS info",
              content: { "application/json": { schema: resolver(Vcs.Info) } },
            },
          },
        }),
        async (c) => {
          const branch = await Vcs.branch();
          return c.json({ branch });
        },
      )
      .get(
        "/command",
        describeRoute({
          summary: "List commands",
          description: "Get all available commands.",
          operationId: "command.list",
          responses: {
            200: {
              description: "List of commands",
              content: { "application/json": { schema: resolver({ type: "array" }) } },
            },
          },
        }),
        async (c) => {
          const commands = await Command.list();
          return c.json(commands);
        },
      )
      .post(
        "/log",
        describeRoute({
          summary: "Write log",
          description: "Write a log entry.",
          operationId: "app.log",
          responses: {
            200: {
              description: "Log entry written",
              content: { "application/json": { schema: resolver({ type: "boolean" }) } },
            },
            ...errors(400),
          },
        }),
        validator("json", {
          service: "string",
          level: "string",
          message: "string",
          extra: { type: "object", optional: true },
        }),
        async (c) => {
          const { service, level, message, extra } = c.req.valid("json");
          const logger = Log.create({ service });
          switch (level) {
            case "debug": logger.debug(message, extra); break;
            case "info": logger.info(message, extra); break;
            case "error": logger.error(message, extra); break;
            case "warn": logger.warn(message, extra); break;
          }
          return c.json(true);
        },
      )
      .get(
        "/agent",
        describeRoute({
          summary: "List agents",
          description: "Get all available AI agents.",
          operationId: "app.agents",
          responses: {
            200: {
              description: "List of agents",
              content: { "application/json": { schema: resolver({ type: "array" }) } },
            },
          },
        }),
        async (c) => {
          const modes = await Agent.list();
          return c.json(modes);
        },
      )
      .get(
        "/skill",
        describeRoute({
          summary: "List skills",
          description: "Get all available skills.",
          operationId: "app.skills",
          responses: {
            200: {
              description: "List of skills",
              content: { "application/json": { schema: resolver({ type: "array" }) } },
            },
          },
        }),
        async (c) => {
          const skills = await Skill.all();
          return c.json(skills);
        },
      )
      .get(
        "/lsp",
        describeRoute({
          summary: "Get LSP status",
          description: "Get LSP server status",
          operationId: "lsp.status",
          responses: {
            200: {
              description: "LSP server status",
              content: { "application/json": { schema: resolver({ type: "array" }) } },
            },
          },
        }),
        async (c) => {
          return c.json(await LSP.status());
        },
      )
      .get(
        "/formatter",
        describeRoute({
          summary: "Get formatter status",
          description: "Get formatter status",
          operationId: "formatter.status",
          responses: {
            200: {
              description: "Formatter status",
              content: { "application/json": { schema: resolver({ type: "array" }) } },
            },
          },
        }),
        async (c) => {
          return c.json(await Format.status());
        },
      )
      .get(
        "/event",
        describeRoute({
          summary: "Subscribe to events",
          description: "Get events via SSE",
          operationId: "event.subscribe",
          responses: {
            200: {
              description: "Event stream",
              content: { "text/event-stream": { schema: resolver(BusEvent.payloads()) } },
            },
          },
        }),
        async (c) => {
          log.info("event connected");
          return streamSSE(c, async (stream) => {
            stream.writeSSE({
              data: JSON.stringify({ type: "server.connected", properties: {} }),
            });
            const unsub = Bus.subscribeAll(async (event) => {
              await stream.writeSSE({ data: JSON.stringify(event) });
              if (event.type === Bus.InstanceDisposed.type) {
                stream.close();
              }
            });

            const heartbeat = setInterval(() => {
              stream.writeSSE({
                data: JSON.stringify({ type: "server.heartbeat", properties: {} }),
              });
            }, 30000);

            await new Promise((resolve) => {
              stream.onAbort(() => {
                clearInterval(heartbeat);
                unsub();
                resolve();
                log.info("event disconnected");
              });
            });
          });
        },
      )
      .all("/*", async (c) => {
        const path = c.req.path;
        const response = await proxy(`https://app.forge.ai${path}`, {
          ...c.req,
          headers: { ...c.req.raw.headers, host: "app.forge.ai" },
        });
        response.headers.set(
          "Content-Security-Policy",
          "default-src 'self'; script-src 'self' 'wasm-unsafe-eval'; style-src 'self' 'unsafe-inline'; img-src 'self' data: https:; font-src 'self' data:; media-src 'self' data:; connect-src 'self' data:",
        );
        return response;
      }),
);

export const openapi = async () => {
  const result = await generateSpecs(App(), {
    documentation: {
      info: { title: "forge", version: "1.0.0", description: "forge api" },
      openapi: "3.1.1",
    },
  });
  return result;
};

export const listen = (opts) => () => {
  _corsWhitelist = opts.cors ?? [];

  const args = {
    hostname: opts.hostname,
    idleTimeout: 0,
    fetch: App().fetch,
    websocket: websocket,
  };
  
  const tryServe = (port) => {
    try {
      return Bun.serve({ ...args, port });
    } catch {
      return undefined;
    }
  };
  
  const server = opts.port === 0 ? (tryServe(4096) ?? tryServe(0)) : tryServe(opts.port);
  if (!server) throw new Error(`Failed to start server on port ${opts.port}`);

  _url = server.url;

  const shouldPublishMDNS =
    opts.mdns &&
    server.port &&
    opts.hostname !== "127.0.0.1" &&
    opts.hostname !== "localhost" &&
    opts.hostname !== "::1";
    
  if (shouldPublishMDNS) {
    MDNS.publish(server.port);
  } else if (opts.mdns) {
    log.warn("mDNS enabled but hostname is loopback; skipping mDNS publish");
  }

  const originalStop = server.stop.bind(server);
  server.stop = async (closeActiveConnections) => {
    if (shouldPublishMDNS) MDNS.unpublish();
    return originalStop(closeActiveConnections);
  };

  return server;
};
