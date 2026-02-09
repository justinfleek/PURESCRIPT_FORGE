// Error Taxonomy FFI - Error code constants
// Production-grade error classification

// Network Errors (1xxx)
exports.NETWORK_UNREACHABLE = 1001;
exports.CONNECTION_TIMEOUT = 1002;
exports.CONNECTION_REFUSED = 1003;
exports.SSL_ERROR = 1004;
exports.DNS_FAILURE = 1005;

// Authentication Errors (2xxx)
exports.INVALID_API_KEY = 2001;
exports.API_KEY_EXPIRED = 2002;
exports.INSUFFICIENT_PERMISSIONS = 2003;
exports.SESSION_EXPIRED = 2004;
exports.TOKEN_INVALID = 2005;

// Rate Limit Errors (3xxx)
exports.RATE_LIMITED_REQUESTS = 3001;
exports.RATE_LIMITED_TOKENS = 3002;
exports.DAILY_LIMIT_REACHED = 3003;
exports.BALANCE_DEPLETED = 3004;

// Validation Errors (4xxx)
exports.INVALID_JSON = 4001;
exports.MISSING_FIELD = 4002;
exports.INVALID_TYPE = 4003;
exports.VALUE_OUT_OF_RANGE = 4004;
exports.MESSAGE_TOO_LARGE = 4005;

// Get current timestamp
exports.getCurrentTimestamp = function() {
  return new Date().toISOString();
};
