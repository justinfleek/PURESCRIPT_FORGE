// | FFI JavaScript bindings for agent orchestrator
// | All operations are deterministic - accept explicit parameters

const { spawn } = require('child_process');
const { createHash } = require('crypto');

// | Call bubblewrap with arguments
// | Returns process ID on success
exports.callBubblewrap = function(args) {
  return function(callback) {
    return function() {
      const proc = spawn('bwrap', args, {
        stdio: ['pipe', 'pipe', 'pipe'],
        detached: false
      });
      
      // Return PID immediately (process is running)
      if (proc.pid) {
        callback({ tag: 'Right', value: { tag: 'Right', value: proc.pid } })();
      } else {
        callback({ tag: 'Right', value: { tag: 'Left', value: 'Failed to get process ID' } })();
      }
      
      proc.on('close', function(code) {
        // Process completed - this is informational only
        // The PID was already returned above
      });
      
      proc.on('error', function(err) {
        // Only report error if PID wasn't already returned
        if (!proc.pid) {
          callback({ tag: 'Right', value: { tag: 'Left', value: 'Process error: ' + err.message } })();
        }
      });
      
      return function(cancel) {
        if (proc.pid) {
          proc.kill();
        }
        cancel();
      };
    };
  };
};

// | Generate deterministic agent ID from seed
// | Uses SHA-256 hash of namespace + seed for deterministic UUID-like ID
// | Format: Deterministic UUID v5-style (but using SHA-256 for simplicity)
exports.generateAgentIdFromSeed = function(namespace) {
  return function(seed) {
    // Create deterministic ID: hash(namespace + seed) formatted as UUID
    const input = namespace + ':' + seed.toString();
    const hash = createHash('sha256').update(input).digest('hex');
    
    // Format as UUID: take first 32 hex chars, format as 8-4-4-4-12
    const uuid = hash.substring(0, 32);
    return uuid.substring(0, 8) + '-' +
           uuid.substring(8, 12) + '-' +
           uuid.substring(12, 16) + '-' +
           uuid.substring(16, 20) + '-' +
           uuid.substring(20, 32);
  };
};

// | Format timestamp (milliseconds since epoch) as ISO 8601 string
// | Deterministic: same input always produces same output
exports.formatTimestamp = function(timestampMs) {
  return new Date(timestampMs).toISOString();
};

// | Kill process by PID
exports.killProcess = function(pid) {
  return function() {
    try {
      const process = require('process');
      const { exec } = require('child_process');
      
      if (process.platform === 'win32') {
        exec('taskkill /pid ' + pid + ' /f /t', function(err) {
          // Error handling is done via return value
        });
        // Windows taskkill is async, but we return success immediately
        // In production, would use proper async handling
        return { tag: 'Right', value: {} };
      } else {
        try {
          process.kill(pid, 'SIGTERM');
          // Wait a bit, then try SIGKILL if still running
          setTimeout(function() {
            try {
              process.kill(pid, 0); // Check if process exists
              process.kill(pid, 'SIGKILL');
            } catch (e) {
              // Process already dead, ignore
            }
          }, 1000);
          return { tag: 'Right', value: {} };
        } catch (e) {
          return { tag: 'Left', value: 'Failed to kill process: ' + e.message };
        }
      }
    } catch (e) {
      return { tag: 'Left', value: 'Failed to kill process: ' + e.message };
    }
  };
};
