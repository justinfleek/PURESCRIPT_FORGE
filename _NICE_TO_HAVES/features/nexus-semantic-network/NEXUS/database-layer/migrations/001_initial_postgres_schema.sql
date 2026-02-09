-- Nexus Database Layer - PostgreSQL Schema Migration
-- Migrates from SQLite schema to PostgreSQL
-- Compatible with Fly.io managed PostgreSQL

-- Enable UUID extension
CREATE EXTENSION IF NOT EXISTS "uuid-ossp";

-- Agents table
CREATE TABLE IF NOT EXISTS agents (
    id TEXT PRIMARY KEY,
    agent_type TEXT NOT NULL,
    config JSONB NOT NULL,
    state JSONB NOT NULL,
    status TEXT NOT NULL CHECK (status IN ('running', 'stopped', 'error')),
    created_at TIMESTAMP NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMP NOT NULL DEFAULT NOW(),
    sandbox_config JSONB,
    working_dir TEXT NOT NULL
);

CREATE INDEX IF NOT EXISTS idx_agents_type ON agents(agent_type);
CREATE INDEX IF NOT EXISTS idx_agents_status ON agents(status);

-- Semantic cells table
CREATE TABLE IF NOT EXISTS semantic_cells (
    id TEXT PRIMARY KEY,
    name TEXT NOT NULL,
    description TEXT NOT NULL,
    level TEXT NOT NULL CHECK (level IN ('primitive', 'basic', 'common')),
    domain TEXT NOT NULL,
    basin TEXT NOT NULL CHECK (basin IN ('entity', 'event', 'property', 'relation', 'cause')),
    state JSONB NOT NULL,  -- CellState: {position: [512 floats], velocity: [512 floats], acceleration: [512 floats], spin: [3 floats], grade: float, energy: float}
    parent_id TEXT,
    children_ids JSONB NOT NULL DEFAULT '[]'::jsonb,  -- Array of cell IDs
    coupling_ids JSONB NOT NULL DEFAULT '[]'::jsonb,  -- Array of coupling IDs
    created_at TIMESTAMP NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMP NOT NULL DEFAULT NOW(),
    FOREIGN KEY (parent_id) REFERENCES semantic_cells(id) ON DELETE SET NULL
);

CREATE INDEX IF NOT EXISTS idx_semantic_cells_level ON semantic_cells(level);
CREATE INDEX IF NOT EXISTS idx_semantic_cells_domain ON semantic_cells(domain);
CREATE INDEX IF NOT EXISTS idx_semantic_cells_basin ON semantic_cells(basin);
CREATE INDEX IF NOT EXISTS idx_semantic_cells_parent ON semantic_cells(parent_id);

-- Couplings table
CREATE TABLE IF NOT EXISTS couplings (
    id TEXT PRIMARY KEY,
    source_id TEXT NOT NULL,
    target_id TEXT NOT NULL,
    coupling_type TEXT NOT NULL CHECK (coupling_type IN ('is_a', 'has', 'causes', 'similar', 'part_of', 'contains', 'near', 'temporal', 'functional')),
    strength DOUBLE PRECISION NOT NULL CHECK (strength >= 0.0 AND strength <= 1.0),
    bidirectional BOOLEAN NOT NULL DEFAULT FALSE,
    created_at TIMESTAMP NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMP NOT NULL DEFAULT NOW(),
    FOREIGN KEY (source_id) REFERENCES semantic_cells(id) ON DELETE CASCADE,
    FOREIGN KEY (target_id) REFERENCES semantic_cells(id) ON DELETE CASCADE,
    CHECK (source_id != target_id)
);

CREATE INDEX IF NOT EXISTS idx_couplings_source ON couplings(source_id);
CREATE INDEX IF NOT EXISTS idx_couplings_target ON couplings(target_id);
CREATE INDEX IF NOT EXISTS idx_couplings_type ON couplings(coupling_type);

-- Network nodes table
CREATE TABLE IF NOT EXISTS network_nodes (
    id TEXT PRIMARY KEY,
    node_type TEXT NOT NULL CHECK (node_type IN ('agent', 'concept', 'entity', 'content')),
    label TEXT NOT NULL,
    properties JSONB NOT NULL DEFAULT '{}'::jsonb,
    created_at TIMESTAMP NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMP NOT NULL DEFAULT NOW()
);

CREATE INDEX IF NOT EXISTS idx_network_nodes_type ON network_nodes(node_type);

-- Network edges table
CREATE TABLE IF NOT EXISTS network_edges (
    id TEXT PRIMARY KEY,
    source_id TEXT NOT NULL,
    target_id TEXT NOT NULL,
    edge_type TEXT NOT NULL,
    weight DOUBLE PRECISION NOT NULL CHECK (weight >= 0.0 AND weight <= 1.0),
    properties JSONB NOT NULL DEFAULT '{}'::jsonb,
    created_at TIMESTAMP NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMP NOT NULL DEFAULT NOW(),
    FOREIGN KEY (source_id) REFERENCES network_nodes(id) ON DELETE CASCADE,
    FOREIGN KEY (target_id) REFERENCES network_nodes(id) ON DELETE CASCADE,
    CHECK (source_id != target_id)
);

CREATE INDEX IF NOT EXISTS idx_network_edges_source ON network_edges(source_id);
CREATE INDEX IF NOT EXISTS idx_network_edges_target ON network_edges(target_id);
CREATE INDEX IF NOT EXISTS idx_network_edges_type ON network_edges(edge_type);

-- Web content table
CREATE TABLE IF NOT EXISTS web_content (
    id TEXT PRIMARY KEY,
    url TEXT NOT NULL UNIQUE,
    content_type TEXT NOT NULL,
    content TEXT NOT NULL,
    title TEXT,
    metadata JSONB,
    fetched_at TIMESTAMP NOT NULL DEFAULT NOW(),
    expires_at TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_web_content_url ON web_content(url);
CREATE INDEX IF NOT EXISTS idx_web_content_fetched ON web_content(fetched_at);

-- Extracted entities table
CREATE TABLE IF NOT EXISTS extracted_entities (
    id TEXT PRIMARY KEY,
    content_id TEXT NOT NULL,
    entity_type TEXT NOT NULL,
    entity_text TEXT NOT NULL,
    confidence DOUBLE PRECISION NOT NULL CHECK (confidence >= 0.0 AND confidence <= 1.0),
    properties JSONB,
    created_at TIMESTAMP NOT NULL DEFAULT NOW(),
    FOREIGN KEY (content_id) REFERENCES web_content(id) ON DELETE CASCADE
);

CREATE INDEX IF NOT EXISTS idx_extracted_entities_content ON extracted_entities(content_id);
CREATE INDEX IF NOT EXISTS idx_extracted_entities_type ON extracted_entities(entity_type);

-- Extracted relations table
CREATE TABLE IF NOT EXISTS extracted_relations (
    id TEXT PRIMARY KEY,
    content_id TEXT NOT NULL,
    source_entity_id TEXT NOT NULL,
    target_entity_id TEXT NOT NULL,
    relation_type TEXT NOT NULL,
    confidence DOUBLE PRECISION NOT NULL CHECK (confidence >= 0.0 AND confidence <= 1.0),
    properties JSONB,
    created_at TIMESTAMP NOT NULL DEFAULT NOW(),
    FOREIGN KEY (content_id) REFERENCES web_content(id) ON DELETE CASCADE,
    FOREIGN KEY (source_entity_id) REFERENCES extracted_entities(id) ON DELETE CASCADE,
    FOREIGN KEY (target_entity_id) REFERENCES extracted_entities(id) ON DELETE CASCADE
);

CREATE INDEX IF NOT EXISTS idx_extracted_relations_content ON extracted_relations(content_id);
CREATE INDEX IF NOT EXISTS idx_extracted_relations_source ON extracted_relations(source_entity_id);
CREATE INDEX IF NOT EXISTS idx_extracted_relations_target ON extracted_relations(target_entity_id);

-- Agent discoveries table (history)
CREATE TABLE IF NOT EXISTS agent_discoveries (
    id TEXT PRIMARY KEY,
    agent_id TEXT NOT NULL,
    discovery_type TEXT NOT NULL CHECK (discovery_type IN ('search_result', 'entity', 'relation', 'connection')),
    discovery_data JSONB NOT NULL,
    discovered_at TIMESTAMP NOT NULL DEFAULT NOW(),
    FOREIGN KEY (agent_id) REFERENCES agents(id) ON DELETE CASCADE
);

CREATE INDEX IF NOT EXISTS idx_agent_discoveries_agent ON agent_discoveries(agent_id);
CREATE INDEX IF NOT EXISTS idx_agent_discoveries_type ON agent_discoveries(discovery_type);
CREATE INDEX IF NOT EXISTS idx_agent_discoveries_discovered ON agent_discoveries(discovered_at);

-- Function to update updated_at timestamp
CREATE OR REPLACE FUNCTION update_updated_at_column()
RETURNS TRIGGER AS $$
BEGIN
    NEW.updated_at = NOW();
    RETURN NEW;
END;
$$ LANGUAGE plpgsql;

-- Triggers to auto-update updated_at
CREATE TRIGGER update_agents_updated_at BEFORE UPDATE ON agents
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

CREATE TRIGGER update_semantic_cells_updated_at BEFORE UPDATE ON semantic_cells
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

CREATE TRIGGER update_couplings_updated_at BEFORE UPDATE ON couplings
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

CREATE TRIGGER update_network_nodes_updated_at BEFORE UPDATE ON network_nodes
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

CREATE TRIGGER update_network_edges_updated_at BEFORE UPDATE ON network_edges
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();
