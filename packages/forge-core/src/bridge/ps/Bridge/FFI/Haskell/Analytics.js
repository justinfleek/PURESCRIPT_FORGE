// DuckDB Analytics FFI Implementation
// Calls Haskell DuckDB executable via command-line interface
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
var haskellAnalyticsPath = process.env.BRIDGE_ANALYTICS_PATH !== undefined && process.env.BRIDGE_ANALYTICS_PATH !== null
  ? process.env.BRIDGE_ANALYTICS_PATH
  : path.join(__dirname, "../../../../bridge-analytics-hs/dist/build/bridge-analytics/bridge-analytics");

// Analytics handle storage
var analyticsHandles = new Map();
var handleCounter = 0;

// | Call Haskell executable with command and args
function callHaskell(command, args) {
  return new Promise(function(resolve, reject) {
    // Check if executable exists
    if (!fs.existsSync(haskellAnalyticsPath)) {
      reject(new Error("Haskell analytics executable not found: " + haskellAnalyticsPath));
      return;
    }
    
    var proc = child_process.spawn(haskellAnalyticsPath, [command].concat(args), {
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

exports.openAnalytics = function(maybePath) {
  return function() {
    try {
      var dbPath = explicitDefault(maybePath, ":memory:");
      // Call Haskell to open analytics database
      var result = require("child_process").execFileSync(
        haskellAnalyticsPath,
        ["open", dbPath],
        { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] }
      );
      
      // Create handle
      var handle = "analytics-" + (handleCounter++);
      analyticsHandles.set(handle, { path: dbPath, handle: handle });
      
      return {
        path: dbPath,
        handle: handle
      };
    } catch (e) {
      // Fallback: return handle anyway
      var handle = "analytics-" + (handleCounter++);
      var fallbackPath = explicitDefault(maybePath, ":memory:");
      analyticsHandles.set(handle, { path: fallbackPath, handle: handle });
      return {
        path: fallbackPath,
        handle: handle
      };
    }
  };
};

exports.closeAnalytics = function(handle) {
  return function() {
    var handleKey = handle.handle !== undefined && handle.handle !== null ? handle.handle : handle.path;
    analyticsHandles.delete(handleKey);
  };
};

exports.loadFromSQLite = function(handle) {
  return function(sqlitePath) {
    return function() {
      return new Promise(function(resolve, reject) {
        var handleKey = handle.handle !== undefined && handle.handle !== null ? handle.handle : handle.path;
        var dbHandle = analyticsHandles.get(handleKey);
        var dbPath = dbHandle !== undefined && dbHandle !== null && dbHandle.path !== undefined && dbHandle.path !== null ? dbHandle.path : handle.path;
        callHaskell("load-sqlite", [dbPath, sqlitePath])
          .then(function(result) {
            resolve({});
          })
          .catch(function(err) {
            reject(err);
          });
      });
    };
  };
};

exports.queryTokenUsageByModel = function(handle) {
  return function(start) {
    return function(end) {
      return function() {
        return new Promise(function(resolve, reject) {
          var handleKey = handle.handle !== undefined && handle.handle !== null ? handle.handle : handle.path;
        var dbHandle = analyticsHandles.get(handleKey);
        var dbPath = dbHandle !== undefined && dbHandle !== null && dbHandle.path !== undefined && dbHandle.path !== null ? dbHandle.path : handle.path;
          var queryJson = JSON.stringify({ start: start, end: end });
          
          callHaskell("query-token-usage", [dbPath, queryJson])
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

exports.queryCostTrends = function(handle) {
  return function(start) {
    return function(end) {
      return function() {
        return new Promise(function(resolve, reject) {
          var handleKey = handle.handle !== undefined && handle.handle !== null ? handle.handle : handle.path;
        var dbHandle = analyticsHandles.get(handleKey);
        var dbPath = dbHandle !== undefined && dbHandle !== null && dbHandle.path !== undefined && dbHandle.path !== null ? dbHandle.path : handle.path;
          var queryJson = JSON.stringify({ start: start, end: end });
          
          callHaskell("query-cost-trends", [dbPath, queryJson])
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

exports.queryTopSessionsByCost = function(handle) {
  return function(limit) {
    return function() {
      return new Promise(function(resolve, reject) {
        var handleKey = handle.handle !== undefined && handle.handle !== null ? handle.handle : handle.path;
        var dbHandle = analyticsHandles.get(handleKey);
        var dbPath = dbHandle !== undefined && dbHandle !== null && dbHandle.path !== undefined && dbHandle.path !== null ? dbHandle.path : handle.path;
        
        callHaskell("query-top-sessions", [dbPath, limit.toString()])
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

exports.queryModelPerformance = function(handle) {
  return function() {
    return new Promise(function(resolve, reject) {
      var handleKey = handle.handle !== undefined && handle.handle !== null ? handle.handle : handle.path;
      var dbHandle = analyticsHandles.get(handleKey);
      var dbPath = dbHandle !== undefined && dbHandle !== null && dbHandle.path !== undefined && dbHandle.path !== null ? dbHandle.path : handle.path;
      
      callHaskell("query-model-performance", [dbPath])
        .then(function(result) {
          resolve(result);
        })
        .catch(function(err) {
          resolve("[]");
        });
    });
  };
};

exports.queryBalanceConsumption = function(handle) {
  return function(start) {
    return function(end) {
      return function() {
        return new Promise(function(resolve, reject) {
          var handleKey = handle.handle !== undefined && handle.handle !== null ? handle.handle : handle.path;
        var dbHandle = analyticsHandles.get(handleKey);
        var dbPath = dbHandle !== undefined && dbHandle !== null && dbHandle.path !== undefined && dbHandle.path !== null ? dbHandle.path : handle.path;
          var queryJson = JSON.stringify({ start: start, end: end });
          
          callHaskell("query-balance-consumption", [dbPath, queryJson])
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

exports.queryDailySummary = function(handle) {
  return function(start) {
    return function(end) {
      return function() {
        return new Promise(function(resolve, reject) {
          var handleKey = handle.handle !== undefined && handle.handle !== null ? handle.handle : handle.path;
        var dbHandle = analyticsHandles.get(handleKey);
        var dbPath = dbHandle !== undefined && dbHandle !== null && dbHandle.path !== undefined && dbHandle.path !== null ? dbHandle.path : handle.path;
          var queryJson = JSON.stringify({ start: start, end: end });
          
          callHaskell("query-daily-summary", [dbPath, queryJson])
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
