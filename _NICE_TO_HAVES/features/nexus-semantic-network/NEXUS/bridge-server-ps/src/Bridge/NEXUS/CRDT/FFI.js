// | FFI JavaScript bindings for CRDT operations
// | Region detection and vector clock management

// | Get current region ID from environment variable REGION
// | Defaults to "local" if not set
exports.getRegionId = function() {
  return process.env.REGION || process.env.FLY_REGION || "local";
};
