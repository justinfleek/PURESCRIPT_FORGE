"use strict";

const { spawn } = require("child_process");
const { promisify } = require("util");
const fs = require("fs").promises;
const path = require("path");
const { exec } = require("child_process");
const execAsync = promisify(exec);

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/**
 * Generate container ID from agent ID
 */
function generateContainerId(agentId) {
  return "nexus-" + agentId;
}

/**
 * Create OCI bundle directory structure
 */
async function createOCIBundle(config, agentId) {
  const baseDir = "/tmp/nexus";
  const bundlePath = path.join(baseDir, "bundles", agentId);
  await fs.mkdir(bundlePath, { recursive: true });
  
  const rootfsPath = path.join(bundlePath, "rootfs");
  await fs.mkdir(rootfsPath, { recursive: true });
  
  // Create minimal rootfs structure
  const dirs = ["bin", "lib", "usr", "tmp", "proc", "sys", "dev"];
  for (const dir of dirs) {
    await fs.mkdir(path.join(rootfsPath, dir), { recursive: true });
  }
  
  // Create working directory in rootfs
  const workingDirRel = config.workingDir.replace(/^\//, "");
  await fs.mkdir(path.join(rootfsPath, workingDirRel), { recursive: true });
  
  // Create OCI config.json
  const ociConfig = {
    ociVersion: "1.0.0",
    process: {
      terminal: false,
      user: { uid: 0, gid: 0 },
      args: ["/bin/sh"], // Will be replaced by exec command
      env: [
        "PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
        "HOME=/root",
        "TERM=xterm"
      ],
      cwd: config.workingDir,
    },
    root: {
      path: "rootfs",
      readonly: false
    },
    mounts: config.allowedDirs.map(dir => ({
      destination: dir.sandboxPath,
      type: "bind",
      source: dir.hostPath,
      options: ["rbind"].concat(dir.readOnly ? ["ro"] : ["rw"])
    })),
    linux: {
      namespaces: [
        { type: "pid" },
        config.networkAccess ? { type: "network" } : { type: "network", path: "" },
        { type: "ipc" },
        { type: "uts" },
        { type: "mount" }
      ],
      resources: {
        devices: []
      }
    }
  };
  
  // Write config.json
  await fs.writeFile(
    path.join(bundlePath, "config.json"),
    JSON.stringify(ociConfig, null, 2)
  );
  
  return bundlePath;
}

/**
 * Run runsc command and return result
 */
function runRunsc(args, options = {}) {
  return new Promise((resolve, reject) => {
    const proc = spawn("runsc", args, {
      stdio: options.stdio || "pipe",
      ...options,
    });
    
    let stdout = "";
    let stderr = "";
    
    if (proc.stdout) {
      proc.stdout.on("data", (data) => {
        stdout += data.toString();
      });
    }
    
    if (proc.stderr) {
      proc.stderr.on("data", (data) => {
        stderr += data.toString();
      });
    }
    
    proc.on("close", (code) => {
      if (code === 0) {
        resolve({ stdout, stderr, code });
      } else {
        reject(new Error(`runsc failed: ${stderr || stdout}`));
      }
    });
    
    proc.on("error", (err) => {
      reject(err);
    });
  });
}

// ============================================================================
// CONTAINER LIFECYCLE
// ============================================================================

/**
 * Create gVisor container
 */
exports.createGVisorContainer = function (config) {
  return function (agentId) {
    return async function () {
      try {
        const containerId = generateContainerId(agentId);
        const bundlePath = await createOCIBundle(config, agentId);
        
        // Run: runsc create <container-id> --bundle <bundle-path>
        await runRunsc([
          "create",
          "--bundle", bundlePath,
          "--platform", "systrap",
          containerId
        ]);
        
        return { tag: "Right", value: { value: containerId } };
      } catch (err) {
        return { tag: "Left", value: err.message };
      }
    };
  };
};

/**
 * Start gVisor container
 */
exports.startGVisorContainer = function (containerId) {
  return async function () {
    try {
      await runRunsc(["start", containerId.value]);
      return { tag: "Right", value: {} };
    } catch (err) {
      return { tag: "Left", value: err.message };
    }
  };
};

/**
 * Execute command in gVisor container
 */
exports.execInGVisorContainer = function (containerId) {
  return function (command) {
    return async function () {
      try {
        const args = ["exec", containerId.value, ...command];
        const result = await runRunsc(args, {
          stdio: ["pipe", "pipe", "pipe"],
        });
        
        return {
          tag: "Right",
          value: {
            stdout: result.stdout || "",
            stderr: result.stderr || "",
            exitCode: result.code || 0,
          },
        };
      } catch (err) {
        return {
          tag: "Left",
          value: err.message,
        };
      }
    };
  };
};

/**
 * Kill gVisor container
 */
exports.killGVisorContainer = function (containerId) {
  return async function () {
    try {
      await runRunsc(["kill", containerId.value, "KILL"]);
      return { tag: "Right", value: {} };
    } catch (err) {
      return { tag: "Left", value: err.message };
    }
  };
};

/**
 * Delete gVisor container
 */
exports.deleteGVisorContainer = function (containerId) {
  return async function () {
    try {
      await runRunsc(["delete", containerId.value]);
      return { tag: "Right", value: {} };
    } catch (err) {
      return { tag: "Left", value: err.message };
    }
  };
};
