"use strict";

const { spawn, exec } = require("child_process");
const { promisify } = require("util");
const fs = require("fs").promises;
const path = require("path");
const crypto = require("crypto");

const execAsync = promisify(exec);

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/**
 * Generate a unique container ID
 */
function generateContainerId() {
  return "gvisor-" + crypto.randomBytes(8).toString("hex");
}

/**
 * Create OCI bundle directory structure
 */
async function createOCIBundle(config, containerId) {
  const bundlePath = path.join(config.rootDir, containerId);
  await fs.mkdir(bundlePath, { recursive: true });
  
  const rootfsPath = path.join(bundlePath, "rootfs");
  await fs.mkdir(rootfsPath, { recursive: true });
  
  // Create config.json (simplified OCI config)
  const ociConfig = {
    ociVersion: "1.0.0",
    process: {
      terminal: false,
      user: { uid: 0, gid: 0 },
      args: config.command || ["/bin/sh"],
      env: config.env.map(e => `${e.key}=${e.value}`),
      cwd: config.workdir || "/",
    },
    root: {
      path: "rootfs",
      readonly: config.rootfs === "ReadOnlyRootfs",
    },
    mounts: config.mounts.map(m => ({
      destination: m.target,
      type: m.mountType === "BindMount" ? "bind" : m.mountType.toLowerCase(),
      source: m.source,
      options: m.readOnly ? ["ro"] : ["rw"],
    })),
    linux: {
      namespaces: [
        { type: "pid" },
        { type: "network" },
        { type: "ipc" },
        { type: "uts" },
        { type: "mount" },
      ],
    },
  };
  
  await fs.writeFile(
    path.join(bundlePath, "config.json"),
    JSON.stringify(ociConfig, null, 2)
  );
  
  return bundlePath;
}

/**
 * Run runsc command and return result
 */
function runRunsc(config, args, options = {}) {
  return new Promise((resolve, reject) => {
    const cmd = [config.runscPath || "/usr/local/bin/runsc", ...args];
    const proc = spawn(cmd[0], cmd.slice(1), {
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
 * Create a new gVisor container
 */
exports.createContainer = function (runtimeConfig) {
  return function (containerConfig) {
    return async function () {
      try {
        const containerId = generateContainerId();
        const bundlePath = await createOCIBundle(containerConfig, containerId);
        
        // Run: runsc create <container-id> --bundle <bundle-path>
        await runRunsc(runtimeConfig, [
          "create",
          containerId,
          "--bundle",
          bundlePath,
          "--platform",
          runtimeConfig.platform || "systrap",
        ]);
        
        return { tag: "Right", value: { value: containerId } };
      } catch (err) {
        return { tag: "Left", value: err.message };
      }
    };
  };
};

/**
 * Get current timestamp in milliseconds
 */
exports.getCurrentTimestamp = function () {
  return Date.now();
};

/**
 * Start a created container
 */
exports.startContainer = function (runtimeConfig) {
  return function (containerId) {
    return async function () {
      try {
        await runRunsc(runtimeConfig, ["start", containerId.value]);
        return { tag: "Right", value: { tag: "Unit" } };
      } catch (err) {
        return { tag: "Left", value: err.message };
      }
    };
  };
};

/**
 * Get current timestamp in milliseconds
 */
exports.getCurrentTimestamp = function () {
  return Date.now();
};

/**
 * Execute a command in a running container
 */
exports.execInContainer = function (runtimeConfig) {
  return function (containerId) {
    return function (command) {
      return async function () {
        try {
          const args = ["exec", containerId.value, ...command];
          const result = await runRunsc(runtimeConfig, args, {
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
};

/**
 * Kill a running container
 */
exports.killContainer = function (runtimeConfig) {
  return function (containerId) {
    return async function () {
      try {
        await runRunsc(runtimeConfig, ["kill", containerId.value, "KILL"]);
        return { tag: "Right", value: {} };
      } catch (err) {
        return { tag: "Left", value: err.message };
      }
    };
  };
};

/**
 * Get current timestamp in milliseconds
 */
exports.getCurrentTimestamp = function () {
  return Date.now();
};

/**
 * Delete a stopped container
 */
exports.deleteContainer = function (runtimeConfig) {
  return function (containerId) {
    return async function () {
      try {
        await runRunsc(runtimeConfig, ["delete", containerId.value]);
        return { tag: "Right", value: { tag: "Unit" } };
      } catch (err) {
        return { tag: "Left", value: err.message };
      }
    };
  };
};

/**
 * Get current timestamp in milliseconds
 */
exports.getCurrentTimestamp = function () {
  return Date.now();
};

// ============================================================================
// CONTAINER INFO
// ============================================================================

/**
 * List all containers
 */
exports.listContainers = function (runtimeConfig) {
  return async function () {
    try {
      const result = await runRunsc(runtimeConfig, ["list", "--format=json"]);
      const containers = JSON.parse(result.stdout);
      
        return {
          tag: "Right",
          value: containers.map((c) => ({
            value: c.id || c.ID,
          })),
        };
    } catch (err) {
      return { tag: "Left", value: err.message };
    }
  };
};

/**
 * Get container status
 */
exports.getContainerStatus = function (runtimeConfig) {
  return function (containerId) {
    return async function () {
      try {
        const result = await runRunsc(runtimeConfig, [
          "state",
          containerId.value,
        ]);
        const state = JSON.parse(result.stdout);
        
        const statusMap = {
          created: "Created",
          running: "Running",
          stopped: "Stopped",
          paused: "Paused",
        };
        
        const status = statusMap[state.status?.toLowerCase()] || `Unknown(${state.status})`;
        return { tag: "Right", value: { tag: status, value: null } };
      } catch (err) {
        return { tag: "Left", value: err.message };
      }
    };
  };
};

/**
 * Get container PID from runsc state
 */
exports.getContainerPid = function (runtimeConfig) {
  return function (containerId) {
    return async function () {
      try {
        const result = await runRunsc(runtimeConfig, [
          "state",
          containerId.value,
        ]);
        const state = JSON.parse(result.stdout);
        
        // runsc state returns JSON with pid field
        // PID is the process ID of the init process in the container
        const pid = state.pid || state.Pid || 0;
        
        if (pid === 0) {
          return { tag: "Left", value: "Container PID not available (container may not be running)" };
        }
        
        return { tag: "Right", value: pid };
      } catch (err) {
        return { tag: "Left", value: err.message };
      }
    };
  };
};

/**
 * Get current timestamp in milliseconds
 */
exports.getCurrentTimestamp = function () {
  return Date.now();
};
