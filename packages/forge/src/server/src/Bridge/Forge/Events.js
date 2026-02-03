// Forge Events FFI Implementation
"use strict";

// Helper: Explicit default value (replaces banned || pattern)
function explicitDefault(value, defaultValue) {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
}

exports.handleForgeEvent = function(store) {
  return function(eventJson) {
    return function() {
      try {
        var event = JSON.parse(eventJson);
        
        switch (event.type) {
          case "session.created":
          case "session.updated":
            // Update session state
            if (event.session) {
              var sessionData = event.session;
              if (store && store.updateSessionPartial) {
                try {
                  store.updateSessionPartial({
                    id: explicitDefault(sessionData.id, null),
                    promptTokens: explicitDefault(sessionData.promptTokens, null),
                    completionTokens: explicitDefault(sessionData.completionTokens, null),
                    totalTokens: explicitDefault(sessionData.totalTokens, null),
                    cost: explicitDefault(sessionData.cost, null),
                    model: explicitDefault(sessionData.model, null),
                    provider: explicitDefault(sessionData.provider, null),
                    messageCount: explicitDefault(sessionData.messageCount, null),
                    updatedAt: sessionData.updatedAt !== undefined && sessionData.updatedAt !== null ? new Date(sessionData.updatedAt).toISOString() : null
                  })();
                } catch (e) {
                  console.error("Failed to update session:", e);
                }
              }
            }
            break;
          
          case "message.created":
          case "message.completed":
            // Update metrics
            if (event.message && event.message.usage) {
              var usage = event.message.usage;
              if (store && store.updateMetricsPartial) {
                try {
                  // Get current metrics to update incrementally
                  var currentMetrics = store.metrics ? store.metrics.value : { totalTokens: 0, totalCost: 0.0, averageResponseTime: 0.0, toolTimings: [] };
                  
                  store.updateMetricsPartial({
                    totalTokens: currentMetrics.totalTokens + explicitDefault(usage.totalTokens, 0),
                    totalCost: currentMetrics.totalCost + explicitDefault(usage.cost, 0.0),
                    averageResponseTime: null, // Would calculate from timing data
                    toolTimings: null // Would update from tool events
                  })();
                } catch (e) {
                  console.error("Failed to update metrics:", e);
                }
              }
            }
            break;
          
          case "tool.execute.after":
            // Update tool timings
            if (event.tool && event.duration) {
              if (store && store.updateMetricsPartial) {
                try {
                  var currentMetrics = store.metrics !== undefined && store.metrics !== null ? store.metrics.value : { toolTimings: [] };
                  var toolTimings = currentMetrics.toolTimings !== undefined && currentMetrics.toolTimings !== null && Array.isArray(currentMetrics.toolTimings) ? currentMetrics.toolTimings : [];
                  
                  var toolName = event.tool.name !== undefined && event.tool.name !== null ? event.tool.name : (event.tool.id !== undefined && event.tool.id !== null ? event.tool.id : "unknown");
                  toolTimings.push({
                    tool: toolName,
                    duration: explicitDefault(event.duration, 0.0)
                  });
                  
                  store.updateMetricsPartial({
                    totalTokens: null,
                    totalCost: null,
                    averageResponseTime: null,
                    toolTimings: toolTimings
                  })();
                } catch (e) {
                  console.error("Failed to update tool timings:", e);
                }
              }
            }
            break;
          
          case "file.read":
            // File read event - could update file context state
            if (event.file && event.content) {
              // File context tracking would go here
              // This would update a file context state if implemented
            }
            break;
          
          case "balance.updated":
            // Balance update event
            if (event.balance) {
              if (store && store.updateBalancePartial) {
                try {
                  store.updateBalancePartial({
                    venice: {
                      diem: explicitDefault(event.balance.diem, null),
                      usd: explicitDefault(event.balance.usd, null),
                      effective: explicitDefault(event.balance.effective, null),
                      lastUpdated: event.balance.lastUpdated !== undefined && event.balance.lastUpdated !== null ? new Date(event.balance.lastUpdated).toISOString() : null
                    },
                    consumptionRate: explicitDefault(event.balance.consumptionRate, null),
                    timeToDepletion: explicitDefault(event.balance.timeToDepletion, null),
                    todayUsed: explicitDefault(event.balance.todayUsed, null),
                    resetCountdown: explicitDefault(event.balance.resetCountdown, null),
                    alertLevel: explicitDefault(event.balance.alertLevel, null)
                  })();
                } catch (e) {
                  console.error("Failed to update balance:", e);
                }
              }
            }
            break;
          
          default:
            // Unknown event type - log but don't error
            if (store && store.logger && store.logger.info) {
              store.logger.info("Unknown Forge event type: " + event.type)();
            }
        }
      } catch (e) {
        console.error("Failed to handle Forge event:", e);
        if (store !== undefined && store !== null && store.logger !== undefined && store.logger !== null && store.logger.error !== undefined && store.logger.error !== null) {
          var errorMessage = e.message !== undefined && e.message !== null ? e.message : String(e);
          store.logger.error("Forge event handling error: " + errorMessage)();
        }
      }
    };
  };
};
