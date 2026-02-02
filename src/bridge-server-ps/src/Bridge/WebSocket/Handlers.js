// WebSocket Handlers FFI Implementation


// Helper: Explicit default value (replaces banned || pattern)
function explicitDefault(value, defaultValue) {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
}

// Helper: Convert JavaScript Date or ISO string to PureScript DateTime structure
function toDateTime(dateOrString) {
  var date = dateOrString instanceof Date ? dateOrString : new Date(dateOrString);
  if (isNaN(date.getTime())) {
    date = new Date();
  }
  return {
    date: {
      year: date.getUTCFullYear(),
      month: date.getUTCMonth() + 1, // JavaScript months are 0-indexed
      day: date.getUTCDate()
    },
    time: {
      hour: date.getUTCHours(),
      minute: date.getUTCMinutes(),
      second: date.getUTCSeconds(),
      millisecond: date.getUTCMilliseconds()
    }
  };
}

export const getState = function(store) {
  return function() {
    // Get state from PureScript store
    // The store has a state Ref containing AppState
    var state = store.state.value;
    return state; // Return AppState object directly
  };
};

export const encodeState = function(state) {
  return function() {
    // Encode AppState to JSON string
    return JSON.stringify({
      connected: state.connected,
      balance: {
        venice: {
          diem: state.balance.venice.diem,
          usd: state.balance.venice.usd,
          effective: state.balance.venice.effective,
          lastUpdated: state.balance.venice.lastUpdated ? state.balance.venice.lastUpdated.toISOString() : null
        },
        consumptionRate: state.balance.consumptionRate,
        timeToDepletion: state.balance.timeToDepletion,
        todayUsed: state.balance.todayUsed,
        todayStartBalance: state.balance.todayStartBalance,
        resetCountdown: state.balance.resetCountdown,
        alertLevel: state.balance.alertLevel
      },
      session: state.session ? {
        id: state.session.id,
        promptTokens: state.session.promptTokens,
        completionTokens: state.session.completionTokens,
        totalTokens: state.session.totalTokens,
        cost: state.session.cost,
        model: state.session.model,
        provider: state.session.provider,
        messageCount: state.session.messageCount,
        startedAt: state.session.startedAt.toISOString(),
        updatedAt: state.session.updatedAt.toISOString()
      } : null,
      proof: {
        connected: state.proof.connected,
        file: state.proof.file,
        position: state.proof.position,
        goals: state.proof.goals,
        diagnostics: state.proof.diagnostics,
        suggestedTactics: state.proof.suggestedTactics
      },
      metrics: {
        totalTokens: state.metrics.totalTokens,
        totalCost: state.metrics.totalCost,
        averageResponseTime: state.metrics.averageResponseTime,
        toolTimings: state.metrics.toolTimings
      }
    });
  };
};

export const handleOpenCodeEvent = function(store) {
  return function(eventJson) {
    return function() {
      // Call the actual OpenCode event handler from Events.js
      // Removed: require("./Bridge/Opencode/Events.js")
      eventsModule.handleOpenCodeEvent(store)(eventJson)();
    };
  };
};

export const decodeChatRequest = function(paramsJson) {
  return function() {
    try {
      var params = JSON.parse(paramsJson);
      return {
        tag: "Right",
        value: {
          model: explicitDefault(params.model, ""),
          messages: explicitDefault(params.messages, []),
          stream: explicitDefault(params.stream, false),
          maxTokens: explicitDefault(params.max_tokens, null),
          temperature: explicitDefault(params.temperature, null)
        }
      };
    } catch (e) {
      var errorMessage = e.message !== undefined && e.message !== null ? e.message : "Invalid request";
      return { tag: "Left", value: errorMessage };
    }
  };
};

export const encodeChatResponse = function(response) {
  return JSON.stringify({
    id: response.id,
    model: response.model,
    choices: response.choices,
    usage: {
      prompt_tokens: response.usage.promptTokens,
      completion_tokens: response.usage.completionTokens,
      total_tokens: response.usage.totalTokens
    }
  });
};

export const encodeStreamResponse = function(response) {
  return JSON.stringify({
    streamId: response.streamId,
    type: response.type_
  });
};

export const generateStreamId = function() {
  return function() {
    return new Promise(function(resolve) {
      var streamId = "stream-" + Date.now() + "-" + Math.random().toString(36).substr(2, 9);
      resolve(streamId);
    });
  };
};

export const processStream = function(ctx) {
  return function(streamId) {
    return function(stream) {
      return function() {
        return new Promise(function(resolve) {
          // Process SSE stream chunks and broadcast to clients
          (async function() {
            try {
              var wsManager = ctx.wsManager !== undefined && ctx.wsManager !== null 
                ? ctx.wsManager 
                : (ctx.notificationService !== undefined && ctx.notificationService !== null && ctx.notificationService.wsManager !== undefined && ctx.notificationService.wsManager !== null
                    ? ctx.notificationService.wsManager
                    : null);
              var iterator = stream;
              
              while (true) {
                var result = await iterator.next();
                
                if (result.done) {
                  // Stream ended
                  var endMessage = JSON.stringify({
                    jsonrpc: "2.0",
                    method: "stream.end",
                    params: { streamId: streamId }
                  });
                  if (wsManager && wsManager.broadcast) {
                    wsManager.broadcast(endMessage)();
                  }
                  break;
                }
                
                var chunk = result.value;
                if (chunk && chunk.tag === "Just" && chunk.value) {
                  // Send chunk notification to all clients
                  var chunkMessage = JSON.stringify({
                    jsonrpc: "2.0",
                    method: "stream.chunk",
                    params: {
                      streamId: streamId,
                      chunk: chunk.value
                    }
                  });
                  if (wsManager && wsManager.broadcast) {
                    wsManager.broadcast(chunkMessage)();
                  }
                }
              }
            } catch (err) {
              console.error("Stream processing error:", err);
              var errorMessage = JSON.stringify({
                jsonrpc: "2.0",
                method: "stream.error",
                params: {
                  streamId: streamId,
                  error: err.message !== undefined && err.message !== null ? err.message : String(err)
                }
              });
              if (ctx.notificationService && ctx.notificationService.wsManager) {
                ctx.notificationService.wsManager.broadcast(errorMessage)();
              }
            }
            resolve({});
          })();
        });
      };
    };
  };
};

export const encodeModels = function(models) {
  return JSON.stringify(models.map(function(m) {
    return {
      id: m.id,
      pricing: {
        input: m.pricing.input,
        output: m.pricing.output
      },
      tier: m.tier,
      context_length: m.contextLength
    };
  }));
};

export const decodeImageRequest = function(paramsJson) {
  return function() {
    try {
      var params = JSON.parse(paramsJson);
      return {
        tag: "Right",
        value: {
          model: explicitDefault(params.model, ""),
          prompt: explicitDefault(params.prompt, ""),
          width: explicitDefault(params.width, null),
          height: explicitDefault(params.height, null)
        }
      };
    } catch (e) {
      var errorMessage = e.message !== undefined && e.message !== null ? e.message : "Invalid request";
      return { tag: "Left", value: errorMessage };
    }
  };
};

export const encodeImageResponse = function(response) {
  return JSON.stringify({
    images: response.images
  });
};

export const dismissNotification = function(service) {
  return function(id) {
    return function() {
      // Call PureScript dismissNotification function
      if (service && service.dismiss) {
        service.dismiss(id)();
      }
    };
  };
};

export const decodeNotificationId = function(paramsJson) {
  return function() {
    try {
      var params = JSON.parse(paramsJson);
      return explicitDefault(params.notificationId, "");
    } catch (e) {
      return "";
    }
  };
};

export const dismissAllNotifications = function(service) {
  return function() {
    // Call PureScript dismissAllNotifications function
    if (service && service.dismissAll) {
      service.dismissAll()();
    }
  };
};

export const decodeSnapshotSaveRequest = function(paramsJson) {
  return function() {
    try {
      var params = JSON.parse(paramsJson);
      return {
        tag: "Right",
        value: {
          trigger: explicitDefault(params.trigger, "manual"),
          description: explicitDefault(params.description, null),
          stateHash: explicitDefault(params.stateHash, "")
        }
      };
    } catch (e) {
      var errorMessage = e.message !== undefined && e.message !== null ? e.message : "Invalid request";
      return { tag: "Left", value: errorMessage };
    }
  };
};

export const decodeSnapshotRestoreRequest = function(paramsJson) {
  return function() {
    try {
      var params = JSON.parse(paramsJson);
      return {
        tag: "Right",
        value: {
          id: explicitDefault(params.id, "")
        }
      };
    } catch (e) {
      var errorMessage = e.message !== undefined && e.message !== null ? e.message : "Invalid request";
      return { tag: "Left", value: errorMessage };
    }
  };
};

export const decodeSnapshotListRequest = function(paramsJson) {
  return function() {
    try {
      var params = paramsJson !== undefined && paramsJson !== null && paramsJson !== "" ? JSON.parse(paramsJson) : {};
      return {
        tag: "Right",
        value: {
          limit: explicitDefault(params.limit, null),
          offset: explicitDefault(params.offset, null)
        }
      };
    } catch (e) {
      return { tag: "Right", value: { limit: null, offset: null } };
    }
  };
};

export const decodeSessionExportRequest = function(paramsJson) {
  return function() {
    try {
      var params = JSON.parse(paramsJson);
      return {
        tag: "Right",
        value: {
          sessionId: explicitDefault(params.sessionId, "")
        }
      };
    } catch (e) {
      var errorMessage = e.message !== undefined && e.message !== null ? e.message : "Invalid request";
      return { tag: "Left", value: errorMessage };
    }
  };
};

export const decodeLeanCheckRequest = function(paramsJson) {
  return function() {
    try {
      var params = JSON.parse(paramsJson);
      return {
        tag: "Right",
        value: {
          file: explicitDefault(params.file, "")
        }
      };
    } catch (e) {
      var errorMessage = e.message !== undefined && e.message !== null ? e.message : "Invalid request";
      return { tag: "Left", value: errorMessage };
    }
  };
};

export const decodeLeanGoalsRequest = function(paramsJson) {
  return function() {
    try {
      var params = JSON.parse(paramsJson);
      return {
        tag: "Right",
        value: {
          file: explicitDefault(params.file, ""),
          line: explicitDefault(params.line, 0),
          column: explicitDefault(params.column, 0)
        }
      };
    } catch (e) {
      var errorMessage = e.message !== undefined && e.message !== null ? e.message : "Invalid request";
      return { tag: "Left", value: errorMessage };
    }
  };
};

export const generateSnapshotId = function() {
  return function() {
    return "snapshot-" + Date.now() + "-" + Math.random().toString(36).substr(2, 9);
  };
};

export const computeStateHash = function(stateJson) {
  return function() {
    // Simple hash function for state
    var hash = 0;
    for (var i = 0; i < stateJson.length; i++) {
      var char = stateJson.charCodeAt(i);
      hash = ((hash << 5) - hash) + char;
      hash = hash & hash; // Convert to 32bit integer
    }
    return Math.abs(hash).toString(36);
  };
};

export const getCurrentTimestamp = function() {
  return function() {
    return new Date().toISOString();
  };
};

// Helper: Convert JavaScript Date or ISO string to PureScript DateTime structure
function toDateTime(dateOrString) {
  var date = dateOrString instanceof Date ? dateOrString : new Date(dateOrString);
  if (isNaN(date.getTime())) {
    date = new Date();
  }
  return {
    date: {
      year: date.getUTCFullYear(),
      month: date.getUTCMonth() + 1, // JavaScript months are 0-indexed
      day: date.getUTCDate()
    },
    time: {
      hour: date.getUTCHours(),
      minute: date.getUTCMinutes(),
      second: date.getUTCSeconds(),
      millisecond: date.getUTCMilliseconds()
    }
  };
}

export const parseSnapshotData = function(snapshotJson) {
  return function() {
    try {
      var snapshot = typeof snapshotJson === "string" ? JSON.parse(snapshotJson) : snapshotJson;
      var stateData = snapshot.stateData !== undefined && snapshot.stateData !== null 
        ? snapshot.stateData 
        : (snapshot.data !== undefined && snapshot.data !== null ? snapshot.data : snapshot);
      
      // Extract file context from state data
      var fileContext = [];
      if (stateData.fileContext !== undefined && stateData.fileContext !== null && Array.isArray(stateData.fileContext)) {
        fileContext = stateData.fileContext.map(function(file) {
          return {
            path: explicitDefault(file.path, ""),
            tokens: explicitDefault(file.tokens, 0),
            language: explicitDefault(file.language, "text")
          };
        });
      }
      
      return {
        balance: stateData.balance !== undefined && stateData.balance !== null ? {
          venice: {
            diem: explicitDefault(stateData.balance.venice.diem, 0.0),
            usd: explicitDefault(stateData.balance.venice.usd, 0.0),
            effective: explicitDefault(stateData.balance.venice.effective, 0.0),
            lastUpdated: stateData.balance.venice.lastUpdated !== undefined && stateData.balance.venice.lastUpdated !== null 
              ? (stateData.balance.venice.lastUpdated instanceof Date || typeof stateData.balance.venice.lastUpdated === "string" 
                  ? toDateTime(stateData.balance.venice.lastUpdated) 
                  : null) 
              : null
          },
          consumptionRate: explicitDefault(stateData.balance.consumptionRate, 0.0),
          timeToDepletion: explicitDefault(stateData.balance.timeToDepletion, null),
          todayUsed: explicitDefault(stateData.balance.todayUsed, 0.0),
          todayStartBalance: explicitDefault(stateData.balance.todayStartBalance, 0.0),
          resetCountdown: explicitDefault(stateData.balance.resetCountdown, null),
          alertLevel: explicitDefault(stateData.balance.alertLevel, "Normal")
        } : null,
        session: stateData.session !== undefined && stateData.session !== null ? {
          id: stateData.session.id,
          promptTokens: explicitDefault(stateData.session.promptTokens, 0),
          completionTokens: explicitDefault(stateData.session.completionTokens, 0),
          totalTokens: explicitDefault(stateData.session.totalTokens, 0),
          cost: explicitDefault(stateData.session.cost, 0.0),
          model: explicitDefault(stateData.session.model, ""),
          provider: explicitDefault(stateData.session.provider, ""),
          messageCount: explicitDefault(stateData.session.messageCount, 0),
          startedAt: toDateTime(stateData.session.startedAt),
          updatedAt: toDateTime(stateData.session.updatedAt)
        } : null,
        proof: stateData.proof !== undefined && stateData.proof !== null ? {
          connected: explicitDefault(stateData.proof.connected, false),
          file: explicitDefault(stateData.proof.file, null),
          position: explicitDefault(stateData.proof.position, null),
          goals: explicitDefault(stateData.proof.goals, []),
          diagnostics: explicitDefault(stateData.proof.diagnostics, []),
          suggestedTactics: explicitDefault(stateData.proof.suggestedTactics, [])
        } : null,
        metrics: stateData.metrics !== undefined && stateData.metrics !== null ? {
          totalTokens: explicitDefault(stateData.metrics.totalTokens, 0),
          totalCost: explicitDefault(stateData.metrics.totalCost, 0.0),
          averageResponseTime: explicitDefault(stateData.metrics.averageResponseTime, 0.0),
          toolTimings: explicitDefault(stateData.metrics.toolTimings, [])
        } : null,
        fileContext: fileContext,
        timestamp: snapshot.timestamp !== undefined && snapshot.timestamp !== null 
          ? snapshot.timestamp 
          : (snapshot.snapshotTimestamp !== undefined && snapshot.snapshotTimestamp !== null 
              ? snapshot.snapshotTimestamp 
              : new Date().toISOString()),
        description: snapshot.description !== undefined && snapshot.description !== null 
          ? snapshot.description 
          : (snapshot.snapshotDescription !== undefined && snapshot.snapshotDescription !== null 
              ? snapshot.snapshotDescription 
              : null)
      };
    } catch (e) {
      console.error("Failed to parse snapshot data:", e);
      return {
        balance: null,
        session: null,
        proof: null,
        metrics: null,
        fileContext: [],
        timestamp: new Date().toISOString(),
        description: null
      };
    }
  };
};

export const encodeSnapshots = function(snapshots) {
  return function() {
    try {
      var snapshotArray = snapshots.map(function(snapJson) {
        var snap = typeof snapJson === "string" ? JSON.parse(snapJson) : snapJson;
        return {
          id: snap.id !== undefined && snap.id !== null ? snap.id : explicitDefault(snap.snapshotId, ""),
          timestamp: snap.timestamp !== undefined && snap.timestamp !== null ? snap.timestamp : explicitDefault(snap.createdAt, ""),
          stateHash: snap.stateHash,
          trigger: explicitDefault(snap.trigger, "manual"),
          description: explicitDefault(snap.description, null)
        };
      });
      return JSON.stringify({ snapshots: snapshotArray });
    } catch (e) {
      console.error("Failed to encode snapshots:", e);
      return JSON.stringify({ snapshots: [] });
    }
  };
};

// | Decode snapshot.get request
export const decodeSnapshotGetRequest = function(paramsJson) {
  return function() {
    if (!paramsJson) {
      return {
        tag: "Left",
        value: "Missing params"
      };
    }
    try {
      var params = JSON.parse(paramsJson);
      return {
        tag: "Right",
        value: {
          id: explicitDefault(params.id, "")
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

// | Encode snapshot.get response
export const encodeSnapshotGetResponse = function(response) {
  return function() {
    try {
      return JSON.stringify({
        id: response.id,
        timestamp: response.timestamp,
        description: response.description,
        state: {
          balance: response.state.balance,
          session: response.state.session,
          proof: response.state.proof,
          metrics: response.state.metrics,
          fileContext: explicitDefault(response.state.fileContext, [])
        }
      });
    } catch (e) {
      console.error("Failed to encode snapshot get response:", e);
      return JSON.stringify({ error: "Failed to encode response" });
    }
  };
};

// | Get file context for snapshot
export const getFileContextForSnapshot = function(store) {
  return function() {
    try {
      // Get current session ID from store
      var state = store.state.value;
      var sessionId = state.session !== undefined && state.session !== null ? state.session.id : null;
      
      // Use FileContext.getContextFiles to get files
      // Removed: require("./Bridge/FFI/Node/FileContext.js")
      var result = FileContext.getContextFiles(store)(sessionId)(null)();
      
      // Transform to snapshot format
      var filesArray = result.files !== undefined && result.files !== null && Array.isArray(result.files) ? result.files : [];
      var files = filesArray.map(function(file) {
        return {
          path: explicitDefault(file.path, ""),
          tokens: explicitDefault(file.tokens, 0),
          language: explicitDefault(file.language, "text")
        };
      });
      
      return files;
    } catch (e) {
      console.error("Failed to get file context for snapshot:", e);
      return [];
    }
  };
};

// | Enrich state JSON with file context
export const enrichStateWithFileContext = function(stateJson) {
  return function(fileContext) {
    return function() {
      try {
        var state = typeof stateJson === "string" ? JSON.parse(stateJson) : stateJson;
        state.fileContext = fileContext !== undefined && fileContext !== null && Array.isArray(fileContext) ? fileContext : [];
        return JSON.stringify(state);
      } catch (e) {
        console.error("Failed to enrich state with file context:", e);
        return stateJson;
      }
    };
  };
};

export const parseSessions = function(sessionsJson) {
  return function() {
    try {
      var sessions = typeof sessionsJson === "string" ? JSON.parse(sessionsJson) : sessionsJson;
      var sessionArray = Array.isArray(sessions) 
        ? sessions 
        : (sessions.sessions !== undefined && sessions.sessions !== null && Array.isArray(sessions.sessions) ? sessions.sessions : []);
      
      return sessionArray.map(function(session) {
        var sessionId = session.id !== undefined && session.id !== null ? session.id : explicitDefault(session.sessionId, "");
        var startedAtValue = session.startedAt !== undefined && session.startedAt !== null ? session.startedAt : explicitDefault(session.createdAt, null);
        var updatedAtValue = session.updatedAt !== undefined && session.updatedAt !== null ? session.updatedAt : explicitDefault(session.modifiedAt, null);
        return {
          id: sessionId,
          promptTokens: explicitDefault(session.promptTokens, 0),
          completionTokens: explicitDefault(session.completionTokens, 0),
          totalTokens: explicitDefault(session.totalTokens, 0),
          cost: explicitDefault(session.cost, 0.0),
          model: explicitDefault(session.model, ""),
          provider: explicitDefault(session.provider, ""),
          messageCount: explicitDefault(session.messageCount, 0),
          startedAt: startedAtValue !== null ? toDateTime(startedAtValue) : toDateTime(new Date()),
          updatedAt: updatedAtValue !== null ? toDateTime(updatedAtValue) : toDateTime(new Date())
        };
      });
    } catch (e) {
      console.error("Failed to parse sessions:", e);
      return [];
    }
  };
};

export const encodeSessionExport = function(session) {
  return function() {
    try {
      return JSON.stringify({
        session: {
          id: session.id,
          promptTokens: session.promptTokens,
          completionTokens: session.completionTokens,
          totalTokens: session.totalTokens,
          cost: session.cost,
          model: session.model,
          provider: session.provider,
          messageCount: session.messageCount,
          startedAt: session.startedAt.toISOString(),
          updatedAt: session.updatedAt.toISOString()
        },
        exportedAt: new Date().toISOString(),
        format: "json"
      });
    } catch (e) {
      console.error("Failed to encode session export:", e);
      return JSON.stringify({ error: "Failed to export session" });
    }
  };
};

export const encodeDiagnostics = function(diagnostics) {
  return function() {
    try {
      return JSON.stringify({
        diagnostics: diagnostics.map(function(diag) {
          return {
            severity: diag.severity,
            message: diag.message,
            range: {
              start: {
                line: diag.range.start.line,
                col: diag.range.start.col
              },
              end: {
                line: diag.range.end.line,
                col: diag.range.end.col
              }
            }
          };
        })
      });
    } catch (e) {
      console.error("Failed to encode diagnostics:", e);
      return JSON.stringify({ diagnostics: [] });
    }
  };
};

export const encodeLeanGoals = function(goals) {
  return function() {
    try {
      return JSON.stringify({
        goals: goals.map(function(goal) {
          return {
            type: goal.type_,
            context: explicitDefault(goal.context, [])
          };
        })
      });
    } catch (e) {
      console.error("Failed to encode Lean goals:", e);
      return JSON.stringify({ goals: [] });
    }
  };
};

// State update functions for snapshot restore
export const updateBalance = function(store) {
  return function(balance) {
    return function() {
      if (store && store.updateBalance) {
        store.updateBalance(balance)();
      }
    };
  };
};

export const updateSession = function(store) {
  return function(session) {
    return function() {
      if (store && store.updateSession) {
        store.updateSession(session)();
      }
    };
  };
};

export const clearSession = function(store) {
  return function() {
    if (store && store.clearSession) {
      store.clearSession()();
    }
  };
};

export const updateProof = function(store) {
  return function(proof) {
    return function() {
      if (store && store.updateProof) {
        store.updateProof(proof)();
      }
    };
  };
};

export const updateMetrics = function(store) {
  return function(metrics) {
    return function() {
      if (store && store.updateMetrics) {
        store.updateMetrics(metrics)();
      }
    };
  };
};

export const updateAlertConfig = function(store) {
  return function(config) {
    return function() {
      if (store && store.updateAlertConfig) {
        store.updateAlertConfig(config)();
      }
    };
  };
};

// Auth token functions (declared in WebSocket.Handlers.purs)
// These are also in Bridge.FFI.Node.Handlers.js, but PureScript needs them here too
var authTokens = new Map();
var TOKEN_EXPIRY_HOURS = 24;

export const generateAuthToken = function() {
  return function() {
    // Removed: require("crypto")
    var token = "auth_" + crypto.randomBytes(32).toString("hex");
    var expires = new Date(Date.now() + TOKEN_EXPIRY_HOURS * 60 * 60 * 1000);
    authTokens.set(token, expires);
    return token;
  };
};

export const getAuthTokenExpiry = function() {
  return function() {
    // Return expiry time for most recent token (or default)
    var expires = new Date(Date.now() + TOKEN_EXPIRY_HOURS * 60 * 60 * 1000);
    return expires.toISOString();
  };
};

export const validateAuthToken = function(token) {
  return function() {
    if (!authTokens.has(token)) {
      return false;
    }
    var expires = authTokens.get(token);
    if (expires < new Date()) {
      authTokens.delete(token);
      return false;
    }
    return true;
  };
};

// | Decode snapshot.get request (also in FFI/Node/Handlers.js, but needed here for consistency)
export const decodeSnapshotGetRequest = function(paramsJson) {
  return function() {
    if (paramsJson === undefined || paramsJson === null || paramsJson === "") {
      return {
        tag: "Left",
        value: "Missing params"
      };
    }
    try {
      var params = JSON.parse(paramsJson);
      return {
        tag: "Right",
        value: {
          id: explicitDefault(params.id, "")
        }
      };
    } catch (e) {
      var errorMessage = e.message !== undefined && e.message !== null ? e.message : "Invalid request";
      return { tag: "Left", value: errorMessage };
    }
  };
};

// | Encode snapshot.get response
export const encodeSnapshotGetResponse = function(response) {
  return function() {
    try {
      var state = response.state;
      return JSON.stringify({
        id: response.id,
        timestamp: response.timestamp,
        description: response.description,
        state: {
          balance: state.balance,
          session: state.session,
          proof: state.proof,
          metrics: state.metrics,
          fileContext: explicitDefault(state.fileContext, [])
        }
      });
    } catch (e) {
      console.error("Failed to encode snapshot get response:", e);
      return JSON.stringify({ error: "Failed to encode snapshot" });
    }
  };
};

// | Get file context for snapshot (from current session)
export const getFileContextForSnapshot = function(store) {
  return function() {
    try {
      // Get current session ID from store
      var state = store.state.value;
      var sessionId = state.session !== undefined && state.session !== null ? state.session.id : null;
      
      // Use FileContext.getContextFiles to get files
      // Removed: require("../FFI/Node/FileContext.js")
      var result = FileContext.getContextFiles(store)(sessionId !== undefined && sessionId !== null ? sessionId : null)(null)();
      
      // Transform to snapshot format
      var filesArray = result.files !== undefined && result.files !== null && Array.isArray(result.files) ? result.files : [];
      var files = filesArray.map(function(file) {
        return {
          path: explicitDefault(file.path, ""),
          tokens: explicitDefault(file.tokens, 0),
          language: explicitDefault(file.language, "text")
        };
      });
      
      return files;
    } catch (e) {
      console.error("Failed to get file context for snapshot:", e);
      return [];
    }
  };
};

// | Enrich state JSON with file context
export const enrichStateWithFileContext = function(stateJson) {
  return function(fileContext) {
    return function() {
      try {
        var state = typeof stateJson === "string" ? JSON.parse(stateJson) : stateJson;
        state.fileContext = fileContext !== undefined && fileContext !== null && Array.isArray(fileContext) ? fileContext : [];
        return JSON.stringify(state);
      } catch (e) {
        console.error("Failed to enrich state with file context:", e);
        return stateJson; // Return original if enrichment fails
      }
    };
  };
};
