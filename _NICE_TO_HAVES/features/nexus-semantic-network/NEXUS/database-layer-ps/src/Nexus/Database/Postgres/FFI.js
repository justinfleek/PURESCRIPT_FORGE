// | FFI JavaScript bindings for PostgreSQL database operations
// | Uses pg library directly for production

const { Pool } = require('pg');

// | Initialize PostgreSQL connection pool from DATABASE_URL
exports.initPostgresPool = function() {
  const databaseUrl = process.env.DATABASE_URL;
  if (!databaseUrl) {
    throw new Error("DATABASE_URL environment variable not set");
  }
  return new Pool({ connectionString: databaseUrl });
};

// | Initialize PostgreSQL connection pool from URL
exports.initPostgresPoolFromUrl = function(databaseUrl) {
  return function() {
    return new Pool({ connectionString: databaseUrl });
  };
};

// | Close PostgreSQL connection pool
exports.closePostgresPool = function(pool) {
  return function() {
    pool.end();
  };
};

// | Execute query and return JSON (via Aff)
exports.executeQueryJson_ = function(pool) {
  return function(query) {
    return function(params) {
      return function() {
        return pool.query(query, params)
          .then(result => ({ tag: 'Right', value: JSON.stringify(result.rows) }))
          .catch(err => ({ tag: 'Left', value: err.message }));
      };
    };
  };
};

// | Query semantic cells
exports.querySemanticCells_ = function(pool) {
  return function(level) {
    return function(domain) {
      return function(basin) {
        return function(limit) {
          return function() {
            let query = "SELECT id, name, description, level, domain, basin, state, parent_id, children_ids, coupling_ids, created_at, updated_at, vector_clock, region_id, last_synced_at FROM semantic_cells WHERE 1=1";
            const params = [];
            let paramIndex = 1;
            
            if (level !== null && level !== undefined) {
              query += ` AND level = $${paramIndex++}`;
              params.push(level);
            }
            if (domain !== null && domain !== undefined) {
              query += ` AND domain = $${paramIndex++}`;
              params.push(domain);
            }
            if (basin !== null && basin !== undefined) {
              query += ` AND basin = $${paramIndex++}`;
              params.push(basin);
            }
            query += " ORDER BY updated_at DESC";
            if (limit !== null && limit !== undefined) {
              query += ` LIMIT $${paramIndex++}`;
              params.push(limit);
            }
            
            return pool.query(query, params)
              .then(result => ({ tag: 'Right', value: JSON.stringify(result.rows) }))
              .catch(err => ({ tag: 'Left', value: err.message }));
          };
        };
      };
    };
  };
};

// | Save semantic cell
exports.saveSemanticCell_ = function(pool) {
  return function(cellJson) {
    return function() {
      const cell = JSON.parse(cellJson);
      const query = `
        INSERT INTO semantic_cells (id, name, description, level, domain, basin, state, parent_id, children_ids, coupling_ids, vector_clock, region_id)
        VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12)
        ON CONFLICT (id) DO UPDATE SET
          name = EXCLUDED.name,
          description = EXCLUDED.description,
          level = EXCLUDED.level,
          domain = EXCLUDED.domain,
          basin = EXCLUDED.basin,
          state = EXCLUDED.state,
          parent_id = EXCLUDED.parent_id,
          children_ids = EXCLUDED.children_ids,
          coupling_ids = EXCLUDED.coupling_ids,
          vector_clock = EXCLUDED.vector_clock,
          region_id = EXCLUDED.region_id,
          updated_at = NOW()
      `;
      const params = [
        cell.id,
        cell.name,
        cell.description,
        cell.level,
        cell.domain,
        cell.basin,
        JSON.stringify(cell.state),
        cell.parentId || null,
        JSON.stringify(cell.childrenIds || []),
        JSON.stringify(cell.couplingIds || []),
        cell.vectorClock ? JSON.stringify(cell.vectorClock) : null,
        cell.regionId || null
      ];
      
      return pool.query(query, params)
        .then(() => ({ tag: 'Right', value: '{}' }))
        .catch(err => ({ tag: 'Left', value: err.message }));
    };
  };
};

// | Load semantic cell by ID
exports.loadSemanticCell_ = function(pool) {
  return function(cellId) {
    return function() {
      const query = "SELECT id, name, description, level, domain, basin, state, parent_id, children_ids, coupling_ids, created_at, updated_at, vector_clock, region_id, last_synced_at FROM semantic_cells WHERE id = $1";
      return pool.query(query, [cellId])
        .then(result => {
          if (result.rows.length === 0) {
            return { tag: 'Right', value: JSON.stringify(null) };
          }
          return { tag: 'Right', value: JSON.stringify(result.rows[0]) };
        })
        .catch(err => ({ tag: 'Left', value: err.message }));
    };
  };
};
