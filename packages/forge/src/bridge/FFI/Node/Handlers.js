// JSON-RPC Request/Response Decoding/Encoding
"use strict";

// Helper: Explicit default value (replaces banned || pattern)
function explicitDefault(value, defaultValue) {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
}

// | Decode session.new request
exports.decodeSessionNewRequest = function(json) {
  return function() {
    try {
      const obj = JSON.parse(json);
      return {
        tag: "Right",
        value: {
          name: explicitDefault(obj.name, null),
          parentId: explicitDefault(obj.parentId, null),
          model: explicitDefault(obj.model, null),
          provider: explicitDefault(obj.provider, null)
        }
      };
    } catch (e) {
      return {
        tag: "Left",
        value: "Invalid JSON: " + e.message
      };
    }
  };
};

// | Decode file.context.add request
exports.decodeFileContextAddRequest = function(json) {
  return function() {
    try {
      const obj = JSON.parse(json);
      return {
        tag: "Right",
        value: {
          path: explicitDefault(obj.path, ""),
          sessionId: explicitDefault(obj.sessionId, null)
        }
      };
    } catch (e) {
      return {
        tag: "Left",
        value: "Invalid JSON: " + e.message
      };
    }
  };
};

// | Decode file.context.list request
exports.decodeFileContextListRequest = function(params) {
  return function() {
    if (!params) {
      return {
        tag: "Right",
        value: {
          sessionId: null,
          filter: null
        }
      };
    }
    try {
      const obj = JSON.parse(params);
      return {
        tag: "Right",
        value: {
          sessionId: explicitDefault(obj.sessionId, null),
          filter: explicitDefault(obj.filter, null)
        }
      };
    } catch (e) {
      return {
        tag: "Left",
        value: "Invalid JSON: " + e.message
      };
    }
  };
};

// | Decode terminal.execute request
exports.decodeTerminalExecuteRequest = function(json) {
  return function() {
    try {
      const obj = JSON.parse(json);
      return {
        tag: "Right",
        value: {
          command: explicitDefault(obj.command, ""),
          cwd: explicitDefault(obj.cwd, null),
          sessionId: explicitDefault(obj.sessionId, null)
        }
      };
    } catch (e) {
      var errorMessage = e.message !== undefined && e.message !== null ? e.message : "Invalid JSON";
      return {
        tag: "Left",
        value: "Invalid JSON: " + errorMessage
      };
    }
  };
};

// | Encode session.new response
exports.encodeSessionNewResponse = function(response) {
  return function() {
    return JSON.stringify({
      sessionId: response.sessionId,
      success: response.success
    });
  };
};

// | Encode file.context.add response
exports.encodeFileContextAddResponse = function(response) {
  return function() {
    return JSON.stringify({
      success: response.success,
      tokens: response.tokens,
      contextBudget: {
        used: response.contextBudget.used,
        total: response.contextBudget.total
      }
    });
  };
};

// | Encode file.context.list response
exports.encodeFileContextListResponse = function(response) {
  return function() {
    return JSON.stringify({
      files: response.files.map(function(file) {
        return {
          path: file.path,
          tokens: file.tokens,
          readAt: file.readAt,
          status: file.status,
          language: file.language,
          size: file.size
        };
      }),
      contextBudget: {
        used: response.contextBudget.used,
        total: response.contextBudget.total
      }
    });
  };
};

// | Encode terminal.execute response
exports.encodeTerminalExecuteResponse = function(response) {
  return function() {
    return JSON.stringify({
      success: response.success,
      output: explicitDefault(response.output, null),
      exitCode: explicitDefault(response.exitCode, null)
    });
  };
};

// | Decode web.search request
exports.decodeWebSearchRequest = function(json) {
  return function() {
    try {
      const obj = JSON.parse(json);
      return {
        tag: "Right",
        value: {
          query: explicitDefault(obj.query, ""),
          maxResults: explicitDefault(obj.maxResults, null),
          sessionId: explicitDefault(obj.sessionId, null)
        }
      };
    } catch (e) {
      return {
        tag: "Left",
        value: "Invalid JSON: " + e.message
      };
    }
  };
};

// | Encode web.search response
exports.encodeWebSearchResponse = function(response) {
  return function() {
    return JSON.stringify({
      success: response.success,
      results: response.results.map(function(result) {
        return {
          title: result.title,
          url: result.url,
          snippet: result.snippet,
          relevance: result.relevance
        };
      }),
      query: response.query,
      totalResults: response.totalResults
    });
  };
};

// | Decode alerts.configure request
exports.decodeAlertsConfigureRequest = function(json) {
  return function() {
    try {
      const obj = JSON.parse(json);
      return {
        tag: "Right",
        value: {
          diemWarningPercent: explicitDefault(obj.diemWarningPercent, 0.20),
          diemCriticalPercent: explicitDefault(obj.diemCriticalPercent, 0.05),
          depletionWarningHours: explicitDefault(obj.depletionWarningHours, 2.0)
        }
      };
    } catch (e) {
      return {
        tag: "Left",
        value: "Invalid JSON: " + e.message
      };
    }
  };
};

// | Generate authentication token
// In-memory token storage
// In production, use secure token storage
var authTokens = new Map();
var TOKEN_EXPIRY_HOURS = 24;

exports.generateAuthToken = function() {
  return function() {
    const crypto = require("crypto");
    const token = "auth_" + crypto.randomBytes(32).toString("hex");
    const expires = new Date(Date.now() + TOKEN_EXPIRY_HOURS * 60 * 60 * 1000);
    authTokens.set(token, expires);
    return token;
  };
};

// | Get authentication token expiry
exports.getAuthTokenExpiry = function() {
  return function() {
    // Return expiry time for most recent token (or default)
    // In production, this would be per-token
    const expires = new Date(Date.now() + TOKEN_EXPIRY_HOURS * 60 * 60 * 1000);
    return expires.toISOString();
  };
};

// | Decode auth.validate request
exports.decodeAuthValidateRequest = function(json) {
  return function() {
    try {
      const obj = JSON.parse(json);
      return {
        tag: "Right",
        value: {
          token: explicitDefault(obj.token, "")
        }
      };
    } catch (e) {
      return {
        tag: "Left",
        value: "Invalid JSON: " + e.message
      };
    }
  };
};

// | Validate authentication token
exports.validateAuthToken = function(token) {
  return function() {
    if (!authTokens.has(token)) {
      return false;
    }
    const expires = authTokens.get(token);
    if (expires < new Date()) {
      authTokens.delete(token);
      return false;
    }
    return true;
  };
};

// | Decode settings.save request
exports.decodeSettingsSaveRequest = function(json) {
  return function() {
    try {
      const obj = JSON.parse(json);
      return {
        tag: "Right",
        value: {
          alerts: {
            warningPercent: obj.alerts !== undefined && obj.alerts !== null ? explicitDefault(obj.alerts.warningPercent, 0.20) : 0.20,
            criticalPercent: obj.alerts !== undefined && obj.alerts !== null ? explicitDefault(obj.alerts.criticalPercent, 0.05) : 0.05,
            warningHours: obj.alerts !== undefined && obj.alerts !== null ? explicitDefault(obj.alerts.warningHours, 2.0) : 2.0,
            soundEnabled: obj.alerts !== undefined && obj.alerts !== null ? explicitDefault(obj.alerts.soundEnabled, false) : false
          },
          appearance: {
            theme: obj.appearance !== undefined && obj.appearance !== null ? explicitDefault(obj.appearance.theme, "dark") : "dark"
          },
          keyboard: {
            enabled: obj.keyboard !== undefined && obj.keyboard !== null ? obj.keyboard.enabled !== false : true,
            vimMode: obj.keyboard !== undefined && obj.keyboard !== null ? obj.keyboard.vimMode !== false : true
          },
          features: {
            countdown: obj.features !== undefined && obj.features !== null ? obj.features.countdown !== false : true,
            tokenCharts: obj.features !== undefined && obj.features !== null ? obj.features.tokenCharts !== false : true,
            proofPanel: obj.features !== undefined && obj.features !== null ? explicitDefault(obj.features.proofPanel, false) : false,
            timeline: obj.features !== undefined && obj.features !== null ? explicitDefault(obj.features.timeline, false) : false
          },
          storage: {
            retentionDays: obj.storage !== undefined && obj.storage !== null ? explicitDefault(obj.storage.retentionDays, 30) : 30
          }
        }
      };
    } catch (e) {
      return {
        tag: "Left",
        value: "Invalid JSON: " + e.message
      };
    }
  };
};

// | Encode settings.save response
exports.encodeSettingsSaveResponse = function(response) {
  return function() {
    return JSON.stringify({
      success: response.success
    });
  };
};

// | Decode snapshot.get request
exports.decodeSnapshotGetRequest = function(paramsJson) {
  return function() {
    if (!paramsJson) {
      return {
        tag: "Left",
        value: "Missing params"
      };
    }
    try {
      const obj = JSON.parse(paramsJson);
      return {
        tag: "Right",
        value: {
          id: explicitDefault(obj.id, "")
        }
      };
    } catch (e) {
      return {
        tag: "Left",
        value: "Invalid JSON: " + e.message
      };
    }
  };
};

// | Decode file.read request
exports.decodeFileReadRequest = function(json) {
  return function() {
    try {
      const obj = JSON.parse(json);
      return {
        tag: "Right",
        value: {
          path: explicitDefault(obj.path, "")
        }
      };
    } catch (e) {
      return {
        tag: "Left",
        value: "Invalid JSON: " + e.message
      };
    }
  };
};

// | Encode file.read response
exports.encodeFileReadResponse = function(response) {
  return function() {
    return JSON.stringify({
      success: response.success,
      content: explicitDefault(response.content, null),
      error: explicitDefault(response.error, null)
    });
  };
};

// | Decode lean.applyTactic request
exports.decodeLeanApplyTacticRequest = function(json) {
  return function() {
    try {
      const obj = JSON.parse(json);
      return {
        tag: "Right",
        value: {
          file: explicitDefault(obj.file, ""),
          line: explicitDefault(obj.line, 0),
          column: explicitDefault(obj.column, 0),
          tactic: explicitDefault(obj.tactic, ""),
          goalIndex: explicitDefault(obj.goalIndex, null)
        }
      };
    } catch (e) {
      return {
        tag: "Left",
        value: "Invalid JSON: " + e.message
      };
    }
  };
};

// | Encode lean.applyTactic response
exports.encodeLeanApplyTacticResponse = function(response) {
  return function() {
    return JSON.stringify({
      success: response.success,
      message: explicitDefault(response.message, null),
      goals: explicitDefault(response.goals, [])
    });
  };
};

// | Decode lean.searchTheorems request
exports.decodeLeanSearchTheoremsRequest = function(json) {
  return function() {
    try {
      const obj = JSON.parse(json);
      return {
        tag: "Right",
        value: {
          query: explicitDefault(obj.query, ""),
          limit: explicitDefault(obj.limit, null),
          file: explicitDefault(obj.file, null)
        }
      };
    } catch (e) {
      return {
        tag: "Left",
        value: "Invalid JSON: " + e.message
      };
    }
  };
};

// | Encode lean.searchTheorems response
exports.encodeLeanSearchTheoremsResponse = function(response) {
  return function() {
    return JSON.stringify({
      theorems: explicitDefault(response.theorems, []),
      total: explicitDefault(response.total, 0)
    });
  };
};
