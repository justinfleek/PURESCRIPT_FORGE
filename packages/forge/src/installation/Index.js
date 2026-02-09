// FFI for Forge.Installation.Index
// 1:1 parity with opencode-dev/packages/opencode/src/installation/index.ts

import { BusEvent } from "../bus/BusEvent.js";
import path from "path";
import { $ } from "bun";
import { NamedError } from "../util/Error.js";
import { Log } from "../util/Log.js";
import { iife } from "../util/IIFE.js";
import { Flag } from "../flag/Flag.js";

const log = Log.create({ service: "installation" });

export const Event = {
  Updated: BusEvent.define(
    "installation.updated",
    { version: "string" },
  ),
  UpdateAvailable: BusEvent.define(
    "installation.update-available",
    { version: "string" },
  ),
};

export const VERSION = typeof FORGE_VERSION === "string" ? FORGE_VERSION : "local";
export const CHANNEL = typeof FORGE_CHANNEL === "string" ? FORGE_CHANNEL : "local";
export const USER_AGENT = `forge/${CHANNEL}/${VERSION}/${Flag.FORGE_CLIENT}`;

export const info = async () => ({
  version: VERSION,
  latest: await latest(await method()),
});

export const isPreview = CHANNEL !== "latest";
export const isLocal = CHANNEL === "local";

export const method = async () => {
  if (process.execPath.includes(path.join(".forge", "bin"))) return "curl";
  if (process.execPath.includes(path.join(".local", "bin"))) return "curl";
  const exec = process.execPath.toLowerCase();

  const checks = [
    { name: "npm", command: () => $`npm list -g --depth=0`.throws(false).quiet().text() },
    { name: "yarn", command: () => $`yarn global list`.throws(false).quiet().text() },
    { name: "pnpm", command: () => $`pnpm list -g --depth=0`.throws(false).quiet().text() },
    { name: "bun", command: () => $`bun pm ls -g`.throws(false).quiet().text() },
    { name: "brew", command: () => $`brew list --formula forge`.throws(false).quiet().text() },
    { name: "scoop", command: () => $`scoop list forge`.throws(false).quiet().text() },
    { name: "choco", command: () => $`choco list --limit-output forge`.throws(false).quiet().text() },
  ];

  checks.sort((a, b) => {
    const aMatches = exec.includes(a.name);
    const bMatches = exec.includes(b.name);
    if (aMatches && !bMatches) return -1;
    if (!aMatches && bMatches) return 1;
    return 0;
  });

  for (const check of checks) {
    const output = await check.command();
    const installedName = check.name === "brew" || check.name === "choco" || check.name === "scoop" 
      ? "forge" 
      : "forge-ai";
    if (output.includes(installedName)) {
      return check.name;
    }
  }

  return "unknown";
};

export const UpgradeFailedError = NamedError.create(
  "UpgradeFailedError",
  { stderr: "string" },
);

async function getBrewFormula() {
  const tapFormula = await $`brew list --formula anomalyco/tap/forge`.throws(false).quiet().text();
  if (tapFormula.includes("forge")) return "anomalyco/tap/forge";
  const coreFormula = await $`brew list --formula forge`.throws(false).quiet().text();
  if (coreFormula.includes("forge")) return "forge";
  return "forge";
}

export const upgrade = (method) => (target) => async () => {
  let cmd;
  switch (method) {
    case "curl":
      cmd = $`curl -fsSL https://forge.ai/install | bash`.env({
        ...process.env,
        VERSION: target,
      });
      break;
    case "npm":
      cmd = $`npm install -g forge-ai@${target}`;
      break;
    case "pnpm":
      cmd = $`pnpm install -g forge-ai@${target}`;
      break;
    case "bun":
      cmd = $`bun install -g forge-ai@${target}`;
      break;
    case "brew": {
      const formula = await getBrewFormula();
      cmd = $`brew upgrade ${formula}`.env({
        HOMEBREW_NO_AUTO_UPDATE: "1",
        ...process.env,
      });
      break;
    }
    case "choco":
      cmd = $`echo Y | choco upgrade forge --version=${target}`;
      break;
    case "scoop":
      cmd = $`scoop install forge@${target}`;
      break;
    default:
      throw new Error(`Unknown method: ${method}`);
  }
  const result = await cmd.quiet().throws(false);
  if (result.exitCode !== 0) {
    const stderr = method === "choco" ? "not running from an elevated command shell" : result.stderr.toString("utf8");
    throw new UpgradeFailedError({ stderr });
  }
  log.info("upgraded", {
    method,
    target,
    stdout: result.stdout.toString(),
    stderr: result.stderr.toString(),
  });
  await $`${process.execPath} --version`.nothrow().quiet().text();
};

export const latest = (installMethod) => async () => {
  const detectedMethod = installMethod || (await method());

  if (detectedMethod === "brew") {
    const formula = await getBrewFormula();
    if (formula === "forge") {
      return fetch("https://formulae.brew.sh/api/formula/forge.json")
        .then((res) => {
          if (!res.ok) throw new Error(res.statusText);
          return res.json();
        })
        .then((data) => data.versions.stable);
    }
  }

  if (detectedMethod === "npm" || detectedMethod === "bun" || detectedMethod === "pnpm") {
    const registry = await iife(async () => {
      const r = (await $`npm config get registry`.quiet().nothrow().text()).trim();
      const reg = r || "https://registry.npmjs.org";
      return reg.endsWith("/") ? reg.slice(0, -1) : reg;
    });
    const channel = CHANNEL;
    return fetch(`${registry}/forge-ai/${channel}`)
      .then((res) => {
        if (!res.ok) throw new Error(res.statusText);
        return res.json();
      })
      .then((data) => data.version);
  }

  if (detectedMethod === "choco") {
    return fetch(
      "https://community.chocolatey.org/api/v2/Packages?$filter=Id%20eq%20%27forge%27%20and%20IsLatestVersion&$select=Version",
      { headers: { Accept: "application/json;odata=verbose" } },
    )
      .then((res) => {
        if (!res.ok) throw new Error(res.statusText);
        return res.json();
      })
      .then((data) => data.d.results[0].Version);
  }

  if (detectedMethod === "scoop") {
    return fetch("https://raw.githubusercontent.com/ScoopInstaller/Main/master/bucket/forge.json", {
      headers: { Accept: "application/json" },
    })
      .then((res) => {
        if (!res.ok) throw new Error(res.statusText);
        return res.json();
      })
      .then((data) => data.version);
  }

  return fetch("https://api.github.com/repos/anomalyco/forge/releases/latest")
    .then((res) => {
      if (!res.ok) throw new Error(res.statusText);
      return res.json();
    })
    .then((data) => data.tag_name.replace(/^v/, ""));
};
