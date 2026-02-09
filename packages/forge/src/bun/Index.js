// FFI for Forge.Bun.Index
// 1:1 parity with opencode-dev/packages/opencode/src/bun/index.ts

import { Global } from "../global/Index.js";
import { Log } from "../util/Log.js";
import path from "path";
import { Filesystem } from "../util/Filesystem.js";
import { NamedError } from "../util/Error.js";
import { readableStreamToText } from "bun";
import { createRequire } from "module";
import { Lock } from "../util/Lock.js";

const log = Log.create({ service: "bun" });
const req = createRequire(import.meta.url);

export const run = (cmd) => (options) => async () => {
  const opts = options || {};
  log.info("running", {
    cmd: [which, ...cmd],
    ...opts,
  });
  const result = Bun.spawn([which, ...cmd], {
    ...opts,
    stdout: "pipe",
    stderr: "pipe",
    env: {
      ...process.env,
      ...opts.env,
      BUN_BE_BUN: "1",
    },
  });
  const code = await result.exited;
  const stdout = result.stdout
    ? typeof result.stdout === "number"
      ? result.stdout
      : await readableStreamToText(result.stdout)
    : undefined;
  const stderr = result.stderr
    ? typeof result.stderr === "number"
      ? result.stderr
      : await readableStreamToText(result.stderr)
    : undefined;
  log.info("done", {
    code,
    stdout,
    stderr,
  });
  if (code !== 0) {
    throw new Error(`Command failed with exit code ${result.exitCode}`);
  }
  return result;
};

export const which = process.execPath;

export const InstallFailedError = NamedError.create(
  "BunInstallFailedError",
  { pkg: "string", version: "string" },
);

export const install = (pkg) => (version) => async () => {
  const ver = version || "latest";
  
  // Use lock to ensure only one install at a time
  using _ = await Lock.write("bun-install");

  const mod = path.join(Global.Path.cache, "node_modules", pkg);
  const pkgjson = Bun.file(path.join(Global.Path.cache, "package.json"));
  const parsed = await pkgjson.json().catch(async () => {
    const result = { dependencies: {} };
    await Bun.write(pkgjson.name, JSON.stringify(result, null, 2));
    return result;
  });
  const dependencies = parsed.dependencies ?? {};
  if (!parsed.dependencies) parsed.dependencies = dependencies;
  const modExists = await Filesystem.exists(mod);
  if (dependencies[pkg] === ver && modExists) return mod;

  const proxied = !!(
    process.env.HTTP_PROXY ||
    process.env.HTTPS_PROXY ||
    process.env.http_proxy ||
    process.env.https_proxy
  );

  const args = [
    "add",
    "--force",
    "--exact",
    ...(proxied ? ["--no-cache"] : []),
    "--cwd",
    Global.Path.cache,
    pkg + "@" + ver,
  ];

  log.info("installing package using Bun's default registry resolution", {
    pkg,
    version: ver,
  });

  await run(args)({
    cwd: Global.Path.cache,
  })().catch((e) => {
    throw new InstallFailedError(
      { pkg, version: ver },
      { cause: e },
    );
  });

  let resolvedVersion = ver;
  if (ver === "latest") {
    const installedPkgJson = Bun.file(path.join(mod, "package.json"));
    const installedPkg = await installedPkgJson.json().catch(() => null);
    if (installedPkg?.version) {
      resolvedVersion = installedPkg.version;
    }
  }

  parsed.dependencies[pkg] = resolvedVersion;
  await Bun.write(pkgjson.name, JSON.stringify(parsed, null, 2));
  return mod;
};
