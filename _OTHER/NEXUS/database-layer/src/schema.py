"""
Nexus Database Layer - Schema Definitions
SQLite (transactional) + DuckDB (analytical) schemas for agent data, semantic memory, and network graphs
"""

import sqlite3
from typing import List, Optional, Dict, Any
from dataclasses import dataclass, asdict
from enum import Enum
import json
from pathlib import Path


class DatabaseType(Enum):
    """Database type"""
    SQLITE = "sqlite"  # Transactional operations
    DUCKDB = "duckdb"  # Analytical queries


@dataclass
class DatabaseConfig:
    """Database configuration"""
    sqlite_path: str  # Path to SQLite database
    duckdb_path: str  # Path to DuckDB database
    create_if_missing: bool = True


class DatabaseSchema:
    """
    Database schema definitions for Nexus.
    
    Tables:
    - agents: Agent configurations and states
    - semantic_cells: Semantic cells (concepts)
    - couplings: Relationships between cells
    - network_nodes: Network graph nodes (agents, concepts, entities, content)
    - network_edges: Network graph edges (relationships)
    - web_content: Web content cache
    - extracted_entities: Extracted entities from content
    - extracted_relations: Extracted relations from content
    - agent_discoveries: Agent discovery history
    """
    
    @staticmethod
    def create_sqlite_schema(conn: sqlite3.Connection) -> None:
        """Create SQLite schema for transactional operations"""
        cursor = conn.cursor()
        
        # Agents table
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS agents (
                id TEXT PRIMARY KEY,
                agent_type TEXT NOT NULL,
                config TEXT NOT NULL,  -- JSON config
                state TEXT NOT NULL,   -- JSON state
                status TEXT NOT NULL,  -- running, stopped, error
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                sandbox_config TEXT,   -- JSON sandbox config
                working_dir TEXT NOT NULL
            )
        """)
        
        # Semantic cells table
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS semantic_cells (
                id TEXT PRIMARY KEY,
                name TEXT NOT NULL,
                description TEXT NOT NULL,
                level TEXT NOT NULL,  -- PRIMITIVE, BASIC, COMMON
                domain TEXT NOT NULL,
                basin TEXT NOT NULL,  -- ENTITY, EVENT, PROPERTY, etc.
                state TEXT NOT NULL,  -- JSON CellState
                parent_id TEXT,
                children_ids TEXT,    -- JSON array
                coupling_ids TEXT,    -- JSON array
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                FOREIGN KEY (parent_id) REFERENCES semantic_cells(id)
            )
        """)
        
        # Couplings table
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS couplings (
                id TEXT PRIMARY KEY,
                source_id TEXT NOT NULL,
                target_id TEXT NOT NULL,
                coupling_type TEXT NOT NULL,  -- IS_A, HAS, CAUSES, etc.
                strength REAL NOT NULL,       -- 0.0 to 1.0
                bidirectional BOOLEAN NOT NULL,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                FOREIGN KEY (source_id) REFERENCES semantic_cells(id),
                FOREIGN KEY (target_id) REFERENCES semantic_cells(id),
                CHECK (source_id != target_id),
                CHECK (strength >= 0.0 AND strength <= 1.0)
            )
        """)
        
        # Network nodes table
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS network_nodes (
                id TEXT PRIMARY KEY,
                node_type TEXT NOT NULL,  -- agent, concept, entity, content
                label TEXT NOT NULL,
                properties TEXT NOT NULL,  -- JSON properties
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL
            )
        """)
        
        # Network edges table
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS network_edges (
                id TEXT PRIMARY KEY,
                source_id TEXT NOT NULL,
                target_id TEXT NOT NULL,
                edge_type TEXT NOT NULL,  -- agent-agent, agent-concept, etc.
                weight REAL NOT NULL,    -- 0.0 to 1.0
                properties TEXT NOT NULL, -- JSON properties
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                FOREIGN KEY (source_id) REFERENCES network_nodes(id),
                FOREIGN KEY (target_id) REFERENCES network_nodes(id),
                CHECK (source_id != target_id),
                CHECK (weight >= 0.0 AND weight <= 1.0)
            )
        """)
        
        # Web content table
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS web_content (
                id TEXT PRIMARY KEY,
                url TEXT NOT NULL UNIQUE,
                content_type TEXT NOT NULL,  -- html, pdf, text, etc.
                content TEXT NOT NULL,      -- Full content or path to file
                title TEXT,
                metadata TEXT,              -- JSON metadata
                fetched_at TEXT NOT NULL,
                expires_at TEXT
            )
        """)
        
        # Extracted entities table
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS extracted_entities (
                id TEXT PRIMARY KEY,
                content_id TEXT NOT NULL,
                entity_type TEXT NOT NULL,  -- person, place, concept, etc.
                entity_text TEXT NOT NULL,
                confidence REAL NOT NULL,   -- 0.0 to 1.0
                properties TEXT,            -- JSON properties
                created_at TEXT NOT NULL,
                FOREIGN KEY (content_id) REFERENCES web_content(id),
                CHECK (confidence >= 0.0 AND confidence <= 1.0)
            )
        """)
        
        # Extracted relations table
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS extracted_relations (
                id TEXT PRIMARY KEY,
                content_id TEXT NOT NULL,
                source_entity_id TEXT NOT NULL,
                target_entity_id TEXT NOT NULL,
                relation_type TEXT NOT NULL,
                confidence REAL NOT NULL,   -- 0.0 to 1.0
                properties TEXT,            -- JSON properties
                created_at TEXT NOT NULL,
                FOREIGN KEY (content_id) REFERENCES web_content(id),
                FOREIGN KEY (source_entity_id) REFERENCES extracted_entities(id),
                FOREIGN KEY (target_entity_id) REFERENCES extracted_entities(id),
                CHECK (confidence >= 0.0 AND confidence <= 1.0)
            )
        """)
        
        # Agent discoveries table (history)
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS agent_discoveries (
                id TEXT PRIMARY KEY,
                agent_id TEXT NOT NULL,
                discovery_type TEXT NOT NULL,  -- search_result, entity, relation, connection
                discovery_data TEXT NOT NULL,  -- JSON discovery data
                discovered_at TEXT NOT NULL,
                FOREIGN KEY (agent_id) REFERENCES agents(id)
            )
        """)
        
        # Indexes for performance
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_agents_type ON agents(agent_type)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_agents_status ON agents(status)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_semantic_cells_level ON semantic_cells(level)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_semantic_cells_domain ON semantic_cells(domain)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_semantic_cells_basin ON semantic_cells(basin)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_couplings_source ON couplings(source_id)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_couplings_target ON couplings(target_id)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_couplings_type ON couplings(coupling_type)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_network_edges_source ON network_edges(source_id)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_network_edges_target ON network_edges(target_id)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_network_edges_type ON network_edges(edge_type)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_web_content_url ON web_content(url)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_extracted_entities_content ON extracted_entities(content_id)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_extracted_relations_content ON extracted_relations(content_id)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_agent_discoveries_agent ON agent_discoveries(agent_id)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_agent_discoveries_type ON agent_discoveries(discovery_type)")
        
        conn.commit()
    
    @staticmethod
    def create_duckdb_schema(conn) -> None:
        """Create DuckDB schema for analytical queries"""
        # DuckDB uses same schema but optimized for OLAP queries
        # We'll create views and materialized tables for analytics
        
        # Create same tables as SQLite
        conn.execute("""
            CREATE TABLE IF NOT EXISTS agents (
                id VARCHAR PRIMARY KEY,
                agent_type VARCHAR NOT NULL,
                config VARCHAR NOT NULL,
                state VARCHAR NOT NULL,
                status VARCHAR NOT NULL,
                created_at TIMESTAMP NOT NULL,
                updated_at TIMESTAMP NOT NULL,
                sandbox_config VARCHAR,
                working_dir VARCHAR NOT NULL
            )
        """)
        
        conn.execute("""
            CREATE TABLE IF NOT EXISTS semantic_cells (
                id VARCHAR PRIMARY KEY,
                name VARCHAR NOT NULL,
                description VARCHAR NOT NULL,
                level VARCHAR NOT NULL,
                domain VARCHAR NOT NULL,
                basin VARCHAR NOT NULL,
                state VARCHAR NOT NULL,
                parent_id VARCHAR,
                children_ids VARCHAR,
                coupling_ids VARCHAR,
                created_at TIMESTAMP NOT NULL,
                updated_at TIMESTAMP NOT NULL
            )
        """)
        
        conn.execute("""
            CREATE TABLE IF NOT EXISTS couplings (
                id VARCHAR PRIMARY KEY,
                source_id VARCHAR NOT NULL,
                target_id VARCHAR NOT NULL,
                coupling_type VARCHAR NOT NULL,
                strength DOUBLE NOT NULL,
                bidirectional BOOLEAN NOT NULL,
                created_at TIMESTAMP NOT NULL,
                updated_at TIMESTAMP NOT NULL
            )
        """)
        
        conn.execute("""
            CREATE TABLE IF NOT EXISTS network_nodes (
                id VARCHAR PRIMARY KEY,
                node_type VARCHAR NOT NULL,
                label VARCHAR NOT NULL,
                properties VARCHAR NOT NULL,
                created_at TIMESTAMP NOT NULL,
                updated_at TIMESTAMP NOT NULL
            )
        """)
        
        conn.execute("""
            CREATE TABLE IF NOT EXISTS network_edges (
                id VARCHAR PRIMARY KEY,
                source_id VARCHAR NOT NULL,
                target_id VARCHAR NOT NULL,
                edge_type VARCHAR NOT NULL,
                weight DOUBLE NOT NULL,
                properties VARCHAR NOT NULL,
                created_at TIMESTAMP NOT NULL,
                updated_at TIMESTAMP NOT NULL
            )
        """)
        
        conn.execute("""
            CREATE TABLE IF NOT EXISTS web_content (
                id VARCHAR PRIMARY KEY,
                url VARCHAR NOT NULL UNIQUE,
                content_type VARCHAR NOT NULL,
                content VARCHAR NOT NULL,
                title VARCHAR,
                metadata VARCHAR,
                fetched_at TIMESTAMP NOT NULL,
                expires_at TIMESTAMP
            )
        """)
        
        conn.execute("""
            CREATE TABLE IF NOT EXISTS extracted_entities (
                id VARCHAR PRIMARY KEY,
                content_id VARCHAR NOT NULL,
                entity_type VARCHAR NOT NULL,
                entity_text VARCHAR NOT NULL,
                confidence DOUBLE NOT NULL,
                properties VARCHAR,
                created_at TIMESTAMP NOT NULL
            )
        """)
        
        conn.execute("""
            CREATE TABLE IF NOT EXISTS extracted_relations (
                id VARCHAR PRIMARY KEY,
                content_id VARCHAR NOT NULL,
                source_entity_id VARCHAR NOT NULL,
                target_entity_id VARCHAR NOT NULL,
                relation_type VARCHAR NOT NULL,
                confidence DOUBLE NOT NULL,
                properties VARCHAR,
                created_at TIMESTAMP NOT NULL
            )
        """)
        
        conn.execute("""
            CREATE TABLE IF NOT EXISTS agent_discoveries (
                id VARCHAR PRIMARY KEY,
                agent_id VARCHAR NOT NULL,
                discovery_type VARCHAR NOT NULL,
                discovery_data VARCHAR NOT NULL,
                discovered_at TIMESTAMP NOT NULL
            )
        """)
        
        # Create analytical views
        conn.execute("""
            CREATE OR REPLACE VIEW network_metrics AS
            SELECT 
                node_type,
                COUNT(*) as node_count,
                AVG(CAST(JSON_EXTRACT(properties, '$.centrality') AS DOUBLE)) as avg_centrality
            FROM network_nodes
            GROUP BY node_type
        """)
        
        conn.execute("""
            CREATE OR REPLACE VIEW coupling_statistics AS
            SELECT 
                coupling_type,
                COUNT(*) as count,
                AVG(strength) as avg_strength,
                MIN(strength) as min_strength,
                MAX(strength) as max_strength
            FROM couplings
            GROUP BY coupling_type
        """)
        
        conn.execute("""
            CREATE OR REPLACE VIEW agent_activity AS
            SELECT 
                agent_id,
                discovery_type,
                COUNT(*) as discovery_count,
                MIN(discovered_at) as first_discovery,
                MAX(discovered_at) as last_discovery
            FROM agent_discoveries
            GROUP BY agent_id, discovery_type
        """)
        
        conn.commit()


def initialize_databases(config: DatabaseConfig) -> tuple:
    """
    Initialize SQLite and DuckDB databases.
    
    Returns:
        (sqlite_conn, duckdb_conn) tuple
    """
    # Create directories if needed
    sqlite_path = Path(config.sqlite_path)
    duckdb_path = Path(config.duckdb_path)
    
    if config.create_if_missing:
        sqlite_path.parent.mkdir(parents=True, exist_ok=True)
        duckdb_path.parent.mkdir(parents=True, exist_ok=True)
    
    # Initialize SQLite
    sqlite_conn = sqlite3.connect(str(sqlite_path))
    sqlite_conn.row_factory = sqlite3.Row
    DatabaseSchema.create_sqlite_schema(sqlite_conn)
    
    # Initialize DuckDB
    try:
        import duckdb
        duckdb_conn = duckdb.connect(str(duckdb_path))
        DatabaseSchema.create_duckdb_schema(duckdb_conn)
    except ImportError:
        # DuckDB not available, return None
        duckdb_conn = None
    
    return (sqlite_conn, duckdb_conn)
