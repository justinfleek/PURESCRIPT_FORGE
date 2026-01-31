// Health check script for Bridge Server
// Checks HTTP endpoint and PostgreSQL connectivity

const http = require('http');
const { Pool } = require('pg');

const PORT = process.env.PORT || 8080;
const DATABASE_URL = process.env.DATABASE_URL;

async function checkHealth() {
  const checks = {
    http: false,
    postgres: false,
  };

  // Check HTTP endpoint
  try {
    const response = await new Promise((resolve, reject) => {
      const req = http.get(`http://localhost:${PORT}/health`, (res) => {
        let data = '';
        res.on('data', (chunk) => { data += chunk; });
        res.on('end', () => {
          resolve({ statusCode: res.statusCode, data });
        });
      });
      req.on('error', reject);
      req.setTimeout(5000, () => reject(new Error('Timeout')));
    });

    if (response.statusCode === 200) {
      checks.http = true;
    }
  } catch (err) {
    console.error('HTTP health check failed:', err.message);
  }

  // Check PostgreSQL connectivity
  if (DATABASE_URL) {
    try {
      const pool = new Pool({ connectionString: DATABASE_URL });
      const result = await pool.query('SELECT 1');
      await pool.end();
      checks.postgres = true;
    } catch (err) {
      console.error('PostgreSQL health check failed:', err.message);
    }
  } else {
    // PostgreSQL check skipped if DATABASE_URL not set
    checks.postgres = true;
  }

  // Exit with error if any check failed
  if (!checks.http || !checks.postgres) {
    console.error('Health checks failed:', checks);
    process.exit(1);
  }

  console.log('All health checks passed:', checks);
  process.exit(0);
}

checkHealth();
