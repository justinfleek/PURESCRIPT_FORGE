-- Nexus Database Layer - Add Distributed Sync Columns
-- Adds columns for distributed semantic memory

-- Add vector clock column to semantic_cells (for CRDT conflict resolution)
ALTER TABLE semantic_cells ADD COLUMN IF NOT EXISTS vector_clock JSONB;

-- Add region_id column (for multi-region deployment)
ALTER TABLE semantic_cells ADD COLUMN IF NOT EXISTS region_id TEXT;

-- Add last_synced_at column (for replication tracking)
ALTER TABLE semantic_cells ADD COLUMN IF NOT EXISTS last_synced_at TIMESTAMP;

-- Add indexes for distributed queries
CREATE INDEX IF NOT EXISTS idx_semantic_cells_region ON semantic_cells(region_id);
CREATE INDEX IF NOT EXISTS idx_semantic_cells_synced ON semantic_cells(last_synced_at);

-- Create semantic_cell_replication table for tracking replication metadata
CREATE TABLE IF NOT EXISTS semantic_cell_replication (
    cell_id TEXT PRIMARY KEY,
    source_region TEXT NOT NULL,
    target_regions TEXT[] NOT NULL DEFAULT ARRAY[]::TEXT[],
    replication_status TEXT NOT NULL CHECK (replication_status IN ('pending', 'syncing', 'synced', 'failed')),
    last_replicated_at TIMESTAMP,
    replication_error TEXT,
    created_at TIMESTAMP NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMP NOT NULL DEFAULT NOW(),
    FOREIGN KEY (cell_id) REFERENCES semantic_cells(id) ON DELETE CASCADE
);

CREATE INDEX IF NOT EXISTS idx_semantic_cell_replication_source ON semantic_cell_replication(source_region);
CREATE INDEX IF NOT EXISTS idx_semantic_cell_replication_status ON semantic_cell_replication(replication_status);
CREATE INDEX IF NOT EXISTS idx_semantic_cell_replication_replicated ON semantic_cell_replication(last_replicated_at);

-- Trigger to auto-update replication updated_at
CREATE TRIGGER update_semantic_cell_replication_updated_at BEFORE UPDATE ON semantic_cell_replication
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();
