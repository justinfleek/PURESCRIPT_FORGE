// FFI for Forge.Plugin.Index
// 1:1 parity with opencode-dev/packages/opencode/src/plugin/index.ts

import { Config } from "../config/Config.js";
import { Bus } from "../bus/Index.js";
import { Log } from "../util/Log.js";
import { createForgeClient } from "../sdk/Index.js";
import { Server } from "../server/Server.js";
import { BunProc } from "../bun/Index.js";
import { Instance } from "../project/Instance.js";
import { Flag } from "../flag/Flag.js";
import { CodexAuthPlugin } from "./Codex.js";
import { Session } from "../session/Index.js";
import { NamedError } from "../util/Error.js";
import { CopilotAuthPlugin } from "./Copilot.js";

const log = Log.create({ service: "plugin" });

const BUILTIN = ["forge-anthropic-auth@0.0.13", "@gitlab/forge-gitlab-auth@1.3.2"];

// Built-in plugins that are directly imported (not installed from npm)
const INTERNAL_PLUGINS = [CodexAuthPlugin, CopilotAuthPlugin];

const state = Instance.state(async () => {
  const client = createForgeClient({
    baseUrl: "http://localhost:4096",
    fetch: async (...args) => Server.App().fetch(...args),
  });
  const config = await Config.get();
  const hooks = [];
  const input = {
    client,
    project: Instance.project,
    worktree: Instance.worktree,
    directory: Instance.directory,
    serverUrl: Server.url(),
    $: Bun.$,
  };

  for (const plugin of INTERNAL_PLUGINS) {
    log.info("loading internal plugin", { name: plugin.name });
    const init = await plugin(input);
    hooks.push(init);
  }

  const plugins = [...(config.plugin ?? [])];
  if (!Flag.FORGE_DISABLE_DEFAULT_PLUGINS) {
    plugins.push(...BUILTIN);
  }

  for (let plugin of plugins) {
    // ignore old codex plugin since it is supported first party now
    if (plugin.includes("forge-openai-codex-auth") || plugin.includes("forge-copilot-auth")) continue;
    log.info("loading plugin", { path: plugin });
    if (!plugin.startsWith("file://")) {
      const lastAtIndex = plugin.lastIndexOf("@");
      const pkg = lastAtIndex > 0 ? plugin.substring(0, lastAtIndex) : plugin;
      const version = lastAtIndex > 0 ? plugin.substring(lastAtIndex + 1) : "latest";
      const builtin = BUILTIN.some((x) => x.startsWith(pkg + "@"));
      plugin = await BunProc.install(pkg, version).catch((err) => {
        if (!builtin) throw err;

        const message = err instanceof Error ? err.message : String(err);
        log.error("failed to install builtin plugin", {
          pkg,
          version,
          error: message,
        });
        Bus.publish(Session.Event.Error, {
          error: new NamedError.Unknown({
            message: `Failed to install built-in plugin ${pkg}@${version}: ${message}`,
          }).toObject(),
        });

        return "";
      });
      if (!plugin) continue;
    }
    const mod = await import(plugin);
    const seen = new Set();
    for (const [_name, fn] of Object.entries(mod)) {
      if (seen.has(fn)) continue;
      seen.add(fn);
      const init = await fn(input);
      hooks.push(init);
    }
  }

  return {
    hooks,
    input,
  };
});

export const trigger = (name) => (input) => (output) => async () => {
  if (!name) return output;
  for (const hook of await state().then((x) => x.hooks)) {
    const fn = hook[name];
    if (!fn) continue;
    await fn(input, output);
  }
  return output;
};

export const list = async () => state().then((x) => x.hooks);

export const init = async () => {
  const hooks = await state().then((x) => x.hooks);
  const config = await Config.get();
  for (const hook of hooks) {
    await hook.config?.(config);
  }
  Bus.subscribeAll(async (input) => {
    const hooks = await state().then((x) => x.hooks);
    for (const hook of hooks) {
      hook["event"]?.({ event: input });
    }
  });
};
