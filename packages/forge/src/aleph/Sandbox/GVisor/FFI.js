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
      env: config.env.map(function (e) { return e.key + "=" + e.value; }),
      cwd: config.workdir || "/",
    },
    root: {
      path: "rootfs",
      readonly: config.rootfs === "ReadOnlyRootfs",
    },
    mounts: config.mounts.map(function (m) {
      return {
        destination: m.target,
        type: m.mountType === "BindMount" ? "bind" : m.mountType.toLowerCase(),
        source: m.source,
        options: m.readOnly ? ["ro"] : ["rw"],
      };
    }),
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
function runRunsc(config, args, options) {
  options = options || {};
  return new Promise(function (resolve, reject) {
    var cmd = [config.runscPath || "/usr/local/bin/runsc"].concat(args);
    var proc = spawn(cmd[0], cmd.slice(1), {
      stdio: options.stdio || "pipe",
    });

    var stdout = "";
    var stderr = "";

    if (proc.stdout) {
      proc.stdout.on("data", function (data) {
        stdout += data.toString();
      });
    }

    if (proc.stderr) {
      proc.stderr.on("data", function (data) {
        stderr += data.toString();
      });
    }

    proc.on("close", function (code) {
      if (code === 0) {
        resolve({ stdout: stdout, stderr: stderr, code: code });
      } else {
        reject(new Error("runsc failed: " + (stderr || stdout)));
      }
    });

    proc.on("error", function (err) {
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
    return function (onError, onSuccess) {
      var containerId = generateContainerId();
      createOCIBundle(containerConfig, containerId)
        .then(function (bundlePath) {
          return runRunsc(runtimeConfig, [
            "create",
            containerId,
            "--bundle",
            bundlePath,
            "--platform",
            runtimeConfig.platform || "systrap",
          ]);
        })
        .then(function () {
          onSuccess({ tag: "Right", value: containerId });
        })
        .catch(function (err) {
          onSuccess({ tag: "Left", value: err.message });
        });
      return function (cancelError, onCancelError, onCancelSuccess) {
        onCancelSuccess();
      };
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
    return function (onError, onSuccess) {
      runRunsc(runtimeConfig, ["start", containerId])
        .then(function () {
          onSuccess({ tag: "Right", value: {} });
        })
        .catch(function (err) {
          onSuccess({ tag: "Left", value: err.message });
        });
      return function (cancelError, onCancelError, onCancelSuccess) {
        onCancelSuccess();
      };
    };
  };
};

/**
 * Execute a command in a running container
 */
exports.execInContainer = function (runtimeConfig) {
  return function (containerId) {
    return function (command) {
      return function (onError, onSuccess) {
        var args = ["exec", containerId].concat(command);
        runRunsc(runtimeConfig, args, { stdio: ["pipe", "pipe", "pipe"] })
          .then(function (result) {
            onSuccess({
              tag: "Right",
              value: {
                stdout: result.stdout || "",
                stderr: result.stderr || "",
                exitCode: result.code || 0,
              },
            });
          })
          .catch(function (err) {
            onSuccess({ tag: "Left", value: err.message });
          });
        return function (cancelError, onCancelError, onCancelSuccess) {
          onCancelSuccess();
        };
      };
    };
  };
};

/**
 * Kill a running container
 */
exports.killContainer = function (runtimeConfig) {
  return function (containerId) {
    return function (onError, onSuccess) {
      runRunsc(runtimeConfig, ["kill", containerId, "KILL"])
        .then(function () {
          onSuccess({ tag: "Right", value: {} });
        })
        .catch(function (err) {
          onSuccess({ tag: "Left", value: err.message });
        });
      return function (cancelError, onCancelError, onCancelSuccess) {
        onCancelSuccess();
      };
    };
  };
};

/**
 * Delete a stopped container
 */
exports.deleteContainer = function (runtimeConfig) {
  return function (containerId) {
    return function (onError, onSuccess) {
      runRunsc(runtimeConfig, ["delete", containerId])
        .then(function () {
          onSuccess({ tag: "Right", value: {} });
        })
        .catch(function (err) {
          onSuccess({ tag: "Left", value: err.message });
        });
      return function (cancelError, onCancelError, onCancelSuccess) {
        onCancelSuccess();
      };
    };
  };
};

// ============================================================================
// CONTAINER INFO
// ============================================================================

/**
 * List all containers
 */
exports.listContainers = function (runtimeConfig) {
  return function (onError, onSuccess) {
    runRunsc(runtimeConfig, ["list", "--format=json"])
      .then(function (result) {
        var containers = JSON.parse(result.stdout);
        onSuccess({
          tag: "Right",
          value: containers.map(function (c) {
            return c.id || c.ID;
          }),
        });
      })
      .catch(function (err) {
        onSuccess({ tag: "Left", value: err.message });
      });
    return function (cancelError, onCancelError, onCancelSuccess) {
      onCancelSuccess();
    };
  };
};

/**
 * Get container status
 */
exports.getContainerStatus = function (runtimeConfig) {
  return function (containerId) {
    return function (onError, onSuccess) {
      runRunsc(runtimeConfig, ["state", containerId])
        .then(function (result) {
          var state = JSON.parse(result.stdout);
          var statusMap = {
            created: "Created",
            running: "Running",
            stopped: "Stopped",
            paused: "Paused",
          };
          var status = state.status ? statusMap[state.status.toLowerCase()] : null;
          if (status) {
            onSuccess({ tag: "Right", value: status });
          } else {
            onSuccess({ tag: "Right", value: "Unknown" });
          }
        })
        .catch(function (err) {
          onSuccess({ tag: "Left", value: err.message });
        });
      return function (cancelError, onCancelError, onCancelSuccess) {
        onCancelSuccess();
      };
    };
  };
};

/**
 * Get container PID from runsc state
 */
exports.getContainerPid = function (runtimeConfig) {
  return function (containerId) {
    return function (onError, onSuccess) {
      runRunsc(runtimeConfig, ["state", containerId])
        .then(function (result) {
          var state = JSON.parse(result.stdout);
          var pid = state.pid || state.Pid || 0;
          if (pid === 0) {
            onSuccess({
              tag: "Left",
              value: "Container PID not available (container may not be running)",
            });
          } else {
            onSuccess({ tag: "Right", value: pid });
          }
        })
        .catch(function (err) {
          onSuccess({ tag: "Left", value: err.message });
        });
      return function (cancelError, onCancelError, onCancelSuccess) {
        onCancelSuccess();
      };
    };
  };
};
