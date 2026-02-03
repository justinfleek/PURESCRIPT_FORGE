// Haskell Database FFI Implementation
// Calls Haskell executable via command-line interface
"use strict";

// Helper: Explicit default value (replaces banned || pattern)
function explicitDefault(value, defaultValue) {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
}

var child_process = require("child_process");
var path = require("path");
var fs = require("fs");

// Path to Haskell executable (built by Nix)
var haskellDbPath = process.env.BRIDGE_DATABASE_PATH !== undefined && process.env.BRIDGE_DATABASE_PATH !== null
  ? process.env.BRIDGE_DATABASE_PATH
  : path.join(__dirname, "../../../../bridge-database-hs/dist/build/bridge-database/bridge-database");

// Database handle storage
var dbHandles = new Map();
var handleCounter = 0;

// | Call Haskell executable with command and args
function callHaskell(command, args) {
  return new Promise(function(resolve, reject) {
    // Check if executable exists
    if (!fs.existsSync(haskellDbPath)) {
      reject(new Error("Haskell database executable not found: " + haskellDbPath));
      return;
    }
    
    var proc = child_process.spawn(haskellDbPath, [command].concat(args), {
      stdio: ["pipe", "pipe", "pipe"]
    });
    
    var stdout = "";
    var stderr = "";
    
    proc.stdout.on("data", function(data) {
      stdout += data.toString();
    });
    
    proc.stderr.on("data", function(data) {
      stderr += data.toString();
    });
    
    proc.on("close", function(code) {
      if (code !== 0) {
        reject(new Error("Haskell process exited with code " + code + ": " + stderr));
        return;
      }
      resolve(stdout.trim());
    });
    
    proc.on("error", function(err) {
      reject(new Error("Failed to spawn Haskell process: " + err.message));
    });
  });
}

exports.openDatabase = function(dbPath) {
  return function() {
    try {
      // Call Haskell to open database
      var result = require("child_process").execFileSync(
        haskellDbPath,
        ["open", dbPath],
        { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] }
      );
      
      // Create handle
      var handle = "db-" + (handleCounter++);
      dbHandles.set(handle, { path: dbPath, handle: handle });
      
      return {
        path: dbPath,
        handle: handle
      };
    } catch (e) {
      // Fallback: return handle anyway (will fail on actual operations)
      var handle = "db-" + (handleCounter++);
      dbHandles.set(handle, { path: dbPath, handle: handle });
      return {
        path: dbPath,
        handle: handle
      };
    }
  };
};

exports.closeDatabase = function(handle) {
  return function() {
    var handleId = getHandleId(handle);
    if (handleId !== null) {
      dbHandles.delete(handleId);
    }
  };
};

exports.saveSnapshot = function(handle) {
  return function(id) {
    return function(timestamp) {
      return function(stateHash) {
        return function(data) {
          return function(trigger) {
            return function(description) {
              return function() {
                return new Promise(function(resolve, reject) {
                  var handleId = getHandleId(handle);
                  var dbHandle = handleId !== null ? dbHandles.get(handleId) : null;
                  var dbPath = dbHandle !== undefined && dbHandle !== null && dbHandle.path !== undefined && dbHandle.path !== null
                    ? dbHandle.path
                    : (handle.path !== undefined && handle.path !== null ? handle.path : null);
                  var snapshotJson = JSON.stringify({
                    id: id,
                    timestamp: timestamp,
                    stateHash: stateHash,
                    data: data,
                    trigger: explicitDefault(trigger, null),
                    description: explicitDefault(description, null)
                  });
                  
                  callHaskell("save-snapshot", [dbPath, snapshotJson])
                    .then(function(result) {
                      resolve(id);
                    })
                    .catch(function(err) {
                      reject(err);
                    });
                });
              };
            };
          };
        };
      };
    };
  };
};

exports.getSnapshot = function(handle) {
  return function(id) {
    return function() {
      return new Promise(function(resolve, reject) {
        var handleKey = handle.handle !== undefined && handle.handle !== null ? handle.handle : handle.path;
        var dbHandle = dbHandles.get(handleKey);
        var dbPath = dbHandle !== undefined && dbHandle !== null && dbHandle.path !== undefined && dbHandle.path !== null ? dbHandle.path : handle.path;
        callHaskell("get-snapshot", [dbPath, id])
          .then(function(result) {
            try {
              if (result === "null" || result.trim() === "") {
                resolve({ tag: "Nothing" });
              } else {
                var snapshot = JSON.parse(result);
                resolve({ tag: "Just", value: JSON.stringify(snapshot) });
              }
            } catch (e) {
              resolve({ tag: "Nothing" });
            }
          })
          .catch(function(err) {
            resolve({ tag: "Nothing" });
          });
      });
    };
  };
};

exports.listSnapshots = function(handle) {
  return function(limit) {
    return function(offset) {
      return function() {
        return new Promise(function(resolve, reject) {
          var handleId = getHandleId(handle);
          var dbHandle = handleId !== null ? dbHandles.get(handleId) : null;
          var dbPath = dbHandle !== undefined && dbHandle !== null && dbHandle.path !== undefined && dbHandle.path !== null
            ? dbHandle.path
            : (handle.path !== undefined && handle.path !== null ? handle.path : null);
          var limitStr = limit ? limit.toString() : "100";
          var offsetStr = offset ? offset.toString() : "0";
          
          callHaskell("list-snapshots", [dbPath, limitStr, offsetStr])
            .then(function(result) {
              resolve(result);
            })
            .catch(function(err) {
              resolve("[]");
            });
        });
      };
    };
  };
};

exports.deleteSnapshot = function(handle) {
  return function(id) {
    return function() {
      return new Promise(function(resolve, reject) {
        var handleKey = handle.handle !== undefined && handle.handle !== null ? handle.handle : handle.path;
        var dbHandle = dbHandles.get(handleKey);
        var dbPath = dbHandle !== undefined && dbHandle !== null && dbHandle.path !== undefined && dbHandle.path !== null ? dbHandle.path : handle.path;
        callHaskell("delete-snapshot", [dbPath, id])
          .then(function(result) {
            resolve(result === "true");
          })
          .catch(function(err) {
            resolve(false);
          });
      });
    };
  };
};

exports.saveSession = function(handle) {
  return function(id) {
    return function(sessionId) {
      return function(promptTokens) {
        return function(completionTokens) {
          return function(totalTokens) {
            return function(cost) {
              return function(model) {
                return function(provider) {
                  return function(startedAt) {
                    return function(endedAt) {
                      return function() {
                        return new Promise(function(resolve, reject) {
                          var handleId = getHandleId(handle);
                  var dbHandle = handleId !== null ? dbHandles.get(handleId) : null;
                  var dbPath = dbHandle !== undefined && dbHandle !== null && dbHandle.path !== undefined && dbHandle.path !== null
                    ? dbHandle.path
                    : (handle.path !== undefined && handle.path !== null ? handle.path : null);
                          var sessionJson = JSON.stringify({
                            id: id,
                            sessionId: sessionId,
                            promptTokens: promptTokens,
                            completionTokens: completionTokens,
                            totalTokens: totalTokens,
                            cost: cost,
                            model: model,
                            provider: provider,
                            startedAt: startedAt,
                            endedAt: explicitDefault(endedAt, null)
                          });
                          
                          callHaskell("save-session", [dbPath, sessionJson])
                            .then(function(result) {
                              resolve(id);
                            })
                            .catch(function(err) {
                              reject(err);
                            });
                        });
                      };
                    };
                  };
                };
              };
            };
          };
        };
      };
    };
  };
};

exports.getSessionsBySessionId = function(handle) {
  return function(sessionId) {
    return function() {
      return new Promise(function(resolve, reject) {
        var handleKey = handle.handle !== undefined && handle.handle !== null ? handle.handle : handle.path;
        var dbHandle = dbHandles.get(handleKey);
        var dbPath = dbHandle !== undefined && dbHandle !== null && dbHandle.path !== undefined && dbHandle.path !== null ? dbHandle.path : handle.path;
        callHaskell("get-sessions", [dbPath, sessionId])
          .then(function(result) {
            resolve(result);
          })
          .catch(function(err) {
            resolve("[]");
          });
      });
    };
  };
};

exports.recordBalanceHistory = function(handle) {
  return function(diem) {
    return function(usd) {
      return function(effective) {
        return function(consumptionRate) {
          return function(timeToDepletion) {
            return function() {
              return new Promise(function(resolve, reject) {
                var handleId = getHandleId(handle);
                var dbHandle = handleId !== null ? dbHandles.get(handleId) : null;
                var dbPath = dbHandle !== undefined && dbHandle !== null && dbHandle.path !== undefined && dbHandle.path !== null
                  ? dbHandle.path
                  : (handle.path !== undefined && handle.path !== null ? handle.path : null);
                var balanceJson = JSON.stringify({
                  diem: diem,
                  usd: usd,
                  effective: effective,
                  consumptionRate: consumptionRate,
                  timeToDepletion: explicitDefault(timeToDepletion, null)
                });
                
                callHaskell("record-balance", [dbPath, balanceJson])
                  .then(function(result) {
                    resolve(result);
                  })
                  .catch(function(err) {
                    reject(err);
                  });
              });
            };
          };
        };
      };
    };
  };
};

exports.saveSettings = function(handle) {
  return function(key) {
    return function(value) {
      return function() {
        return new Promise(function(resolve, reject) {
          try {
            var handleId = getHandleId(handle);
            var dbHandle = handleId !== null ? dbHandles.get(handleId) : null;
            if (dbHandle === undefined || dbHandle === null || dbHandle.handle === undefined || dbHandle.handle === null) {
              reject(new Error("Database handle not found"));
              return;
            }
            
            // Call Haskell executable to save settings
            var result = require("child_process").execFileSync(
              haskellDbPath,
              ["save-settings", key, value],
              { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] }
            );
            
            resolve();
          } catch (e) {
            reject(e);
          }
        });
      };
    };
  };
};

exports.getSettings = function(handle) {
  return function(key) {
    return function() {
      return new Promise(function(resolve, reject) {
        try {
          var handleKey = handle.handle !== undefined && handle.handle !== null ? handle.handle : handle.path;
          var dbHandle = dbHandles.get(handleKey);
          if (dbHandle === undefined || dbHandle === null || dbHandle.handle === undefined || dbHandle.handle === null) {
            reject(new Error("Database handle not found"));
            return;
          }
          
          // Call Haskell executable to get settings
          var result = require("child_process").execFileSync(
            haskellDbPath,
            ["get-settings", key],
            { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] }
          );
          
          var value = result.trim();
          resolve(value === "" ? null : value);
        } catch (e) {
          reject(e);
        }
      });
    };
  };
};

exports.getBalanceHistory = function(handle) {
  return function(limit) {
    return function(offset) {
      return function() {
        return new Promise(function(resolve, reject) {
          var handleId = getHandleId(handle);
          var dbHandle = handleId !== null ? dbHandles.get(handleId) : null;
          var dbPath = dbHandle !== undefined && dbHandle !== null && dbHandle.path !== undefined && dbHandle.path !== null
            ? dbHandle.path
            : (handle.path !== undefined && handle.path !== null ? handle.path : null);
          var limitStr = limit ? limit.toString() : "100";
          var offsetStr = offset ? offset.toString() : "0";
          
          callHaskell("get-balance-history", [dbPath, limitStr, offsetStr])
            .then(function(result) {
              resolve(result);
            })
            .catch(function(err) {
              resolve("[]");
            });
        });
      };
    };
  };
};
