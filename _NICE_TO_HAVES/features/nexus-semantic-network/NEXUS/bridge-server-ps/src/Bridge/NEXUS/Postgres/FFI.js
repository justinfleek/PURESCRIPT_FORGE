// | FFI JavaScript bindings for PostgreSQL pool management
// | Uses pg library directly for production

const { Pool } = require('pg');

// | Global PostgreSQL pool (initialized at server startup)
let postgresPool = null;

// | Initialize PostgreSQL pool (called at server startup)
// | Reads DATABASE_URL from environment (set by Fly.io)
exports.initPostgresPool = function() {
  if (postgresPool === null) {
    const databaseUrl = process.env.DATABASE_URL;
    if (!databaseUrl) {
      throw new Error("DATABASE_URL environment variable not set");
    }
    postgresPool = new Pool({ connectionString: databaseUrl });
  }
  return postgresPool;
};

// | Initialize PostgreSQL pool from URL
exports.initPostgresPoolFromUrl = function(databaseUrl) {
  return function() {
    if (postgresPool === null) {
      postgresPool = new Pool({ connectionString: databaseUrl });
    }
    return postgresPool;
  };
};

// | Get PostgreSQL pool
exports.getPostgresPool = function() {
  if (postgresPool === null) {
    // Initialize if not already initialized (reads DATABASE_URL from env)
    return exports.initPostgresPool();
  }
  return postgresPool;
};

// | Close PostgreSQL pool (called at server shutdown)
exports.closePostgresPool = function() {
  if (postgresPool !== null) {
    postgresPool.end();
    postgresPool = null;
  }
};
