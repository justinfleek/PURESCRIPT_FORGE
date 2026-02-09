"use strict";

/**
 * Task Scheduler FFI
 * In-memory cron-like task scheduler using setInterval
 */

// Active tasks: Map<taskId, { task, timer }>
var activeTasks = new Map();

// | Parse a simple cron interval to milliseconds
// Supports: @every Ns, @every Nm, @every Nh
function parseCronToMs(cron) {
  var match = cron.match(/@every\s+(\d+)([smh])/);
  if (match) {
    var value = parseInt(match[1], 10);
    switch (match[2]) {
      case "s": return value * 1000;
      case "m": return value * 60 * 1000;
      case "h": return value * 60 * 60 * 1000;
    }
  }
  // Default: 60 seconds
  return 60000;
}

// | Schedule a task
exports.scheduleFFI = function (task) {
  return function (onError, onSuccess) {
    try {
      // Cancel existing task with same ID
      if (activeTasks.has(task.id)) {
        clearInterval(activeTasks.get(task.id).timer);
      }

      if (task.enabled) {
        var intervalMs = parseCronToMs(task.cron);
        var timer = setInterval(function () {
          // Emit task execution event
          if (typeof process !== "undefined" && process.emit) {
            process.emit("forge:scheduler:tick", {
              taskId: task.id,
              taskName: task.name,
              timestamp: Date.now(),
            });
          }
        }, intervalMs);

        // Don't block process exit
        if (timer.unref) timer.unref();

        activeTasks.set(task.id, { task: task, timer: timer });
      } else {
        activeTasks.set(task.id, { task: task, timer: null });
      }

      onSuccess({ tag: "Right", value: undefined });
    } catch (e) {
      onSuccess({ tag: "Left", value: "Failed to schedule task: " + e.message });
    }

    return function (cancelError, onCancelerError, onCancelerSuccess) {
      onCancelerSuccess();
    };
  };
};

// | Cancel a task
exports.cancelFFI = function (taskId) {
  return function (onError, onSuccess) {
    try {
      var entry = activeTasks.get(taskId);
      if (entry) {
        if (entry.timer) clearInterval(entry.timer);
        activeTasks.delete(taskId);
      }
      onSuccess({ tag: "Right", value: undefined });
    } catch (e) {
      onSuccess({ tag: "Left", value: "Failed to cancel task: " + e.message });
    }

    return function (cancelError, onCancelerError, onCancelerSuccess) {
      onCancelerSuccess();
    };
  };
};

// | List all tasks
exports.listFFI = function (onError, onSuccess) {
  try {
    var tasks = [];
    activeTasks.forEach(function (entry) {
      tasks.push(entry.task);
    });
    onSuccess({ tag: "Right", value: tasks });
  } catch (e) {
    onSuccess({ tag: "Left", value: "Failed to list tasks: " + e.message });
  }

  return function (cancelError, onCancelerError, onCancelerSuccess) {
    onCancelerSuccess();
  };
};
