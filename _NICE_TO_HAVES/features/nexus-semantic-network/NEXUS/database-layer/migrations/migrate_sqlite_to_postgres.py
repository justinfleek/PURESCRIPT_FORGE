"""
Nexus Database Layer - SQLite to PostgreSQL Migration Script
Migrates data from SQLite database to PostgreSQL
"""

import sys
import sqlite3
import json
import argparse
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Any

try:
    import psycopg2
    from psycopg2.extras import execute_values
except ImportError:
    print("Error: psycopg2 not installed. Install with: pip install psycopg2-binary")
    sys.exit(1)


def migrate_agents(sqlite_conn, pg_conn):
    """Migrate agents table"""
    sqlite_cursor = sqlite_conn.cursor()
    pg_cursor = pg_conn.cursor()
    
    sqlite_cursor.execute("SELECT * FROM agents")
    rows = sqlite_cursor.fetchall()
    
    if not rows:
        print("No agents to migrate")
        return
    
    data = []
    for row in rows:
        data.append((
            row["id"],
            row["agent_type"],
            json.dumps(json.loads(row["config"])),  # Ensure valid JSON
            json.dumps(json.loads(row["state"])),
            row["status"],
            row["created_at"],
            row["updated_at"],
            json.dumps(json.loads(row["sandbox_config"])) if row["sandbox_config"] else None,
            row["working_dir"]
        ))
    
    execute_values(
        pg_cursor,
        """INSERT INTO agents (id, agent_type, config, state, status, created_at, updated_at, sandbox_config, working_dir)
           VALUES %s ON CONFLICT (id) DO UPDATE SET
           agent_type = EXCLUDED.agent_type,
           config = EXCLUDED.config,
           state = EXCLUDED.state,
           status = EXCLUDED.status,
           updated_at = EXCLUDED.updated_at,
           sandbox_config = EXCLUDED.sandbox_config,
           working_dir = EXCLUDED.working_dir""",
        data
    )
    
    pg_conn.commit()
    print(f"Migrated {len(data)} agents")


def migrate_semantic_cells(sqlite_conn, pg_conn):
    """Migrate semantic_cells table"""
    sqlite_cursor = sqlite_conn.cursor()
    pg_cursor = pg_conn.cursor()
    
    sqlite_cursor.execute("SELECT * FROM semantic_cells")
    rows = sqlite_cursor.fetchall()
    
    if not rows:
        print("No semantic cells to migrate")
        return
    
    data = []
    for row in rows:
        # Parse JSON fields
        state = json.loads(row["state"])
        children_ids = json.loads(row["children_ids"]) if row["children_ids"] else []
        coupling_ids = json.loads(row["coupling_ids"]) if row["coupling_ids"] else []
        
        data.append((
            row["id"],
            row["name"],
            row["description"],
            row["level"],
            row["domain"],
            row["basin"],
            json.dumps(state),
            row["parent_id"],
            json.dumps(children_ids),
            json.dumps(coupling_ids),
            row["created_at"],
            row["updated_at"]
        ))
    
    execute_values(
        pg_cursor,
        """INSERT INTO semantic_cells (id, name, description, level, domain, basin, state, parent_id, children_ids, coupling_ids, created_at, updated_at)
           VALUES %s ON CONFLICT (id) DO UPDATE SET
           name = EXCLUDED.name,
           description = EXCLUDED.description,
           level = EXCLUDED.level,
           domain = EXCLUDED.domain,
           basin = EXCLUDED.basin,
           state = EXCLUDED.state,
           parent_id = EXCLUDED.parent_id,
           children_ids = EXCLUDED.children_ids,
           coupling_ids = EXCLUDED.coupling_ids,
           updated_at = EXCLUDED.updated_at""",
        data
    )
    
    pg_conn.commit()
    print(f"Migrated {len(data)} semantic cells")


def migrate_couplings(sqlite_conn, pg_conn):
    """Migrate couplings table"""
    sqlite_cursor = sqlite_conn.cursor()
    pg_cursor = pg_conn.cursor()
    
    sqlite_cursor.execute("SELECT * FROM couplings")
    rows = sqlite_cursor.fetchall()
    
    if not rows:
        print("No couplings to migrate")
        return
    
    data = []
    for row in rows:
        data.append((
            row["id"],
            row["source_id"],
            row["target_id"],
            row["coupling_type"],
            float(row["strength"]),
            bool(row["bidirectional"]),
            row["created_at"],
            row["updated_at"]
        ))
    
    execute_values(
        pg_cursor,
        """INSERT INTO couplings (id, source_id, target_id, coupling_type, strength, bidirectional, created_at, updated_at)
           VALUES %s ON CONFLICT (id) DO UPDATE SET
           source_id = EXCLUDED.source_id,
           target_id = EXCLUDED.target_id,
           coupling_type = EXCLUDED.coupling_type,
           strength = EXCLUDED.strength,
           bidirectional = EXCLUDED.bidirectional,
           updated_at = EXCLUDED.updated_at""",
        data
    )
    
    pg_conn.commit()
    print(f"Migrated {len(data)} couplings")


def migrate_network_nodes(sqlite_conn, pg_conn):
    """Migrate network_nodes table"""
    sqlite_cursor = sqlite_conn.cursor()
    pg_cursor = pg_conn.cursor()
    
    sqlite_cursor.execute("SELECT * FROM network_nodes")
    rows = sqlite_cursor.fetchall()
    
    if not rows:
        print("No network nodes to migrate")
        return
    
    data = []
    for row in rows:
        properties = json.loads(row["properties"]) if row["properties"] else {}
        data.append((
            row["id"],
            row["node_type"],
            row["label"],
            json.dumps(properties),
            row["created_at"],
            row["updated_at"]
        ))
    
    execute_values(
        pg_cursor,
        """INSERT INTO network_nodes (id, node_type, label, properties, created_at, updated_at)
           VALUES %s ON CONFLICT (id) DO UPDATE SET
           node_type = EXCLUDED.node_type,
           label = EXCLUDED.label,
           properties = EXCLUDED.properties,
           updated_at = EXCLUDED.updated_at""",
        data
    )
    
    pg_conn.commit()
    print(f"Migrated {len(data)} network nodes")


def migrate_network_edges(sqlite_conn, pg_conn):
    """Migrate network_edges table"""
    sqlite_cursor = sqlite_conn.cursor()
    pg_cursor = pg_conn.cursor()
    
    sqlite_cursor.execute("SELECT * FROM network_edges")
    rows = sqlite_cursor.fetchall()
    
    if not rows:
        print("No network edges to migrate")
        return
    
    data = []
    for row in rows:
        properties = json.loads(row["properties"]) if row["properties"] else {}
        data.append((
            row["id"],
            row["source_id"],
            row["target_id"],
            row["edge_type"],
            float(row["weight"]),
            json.dumps(properties),
            row["created_at"],
            row["updated_at"]
        ))
    
    execute_values(
        pg_cursor,
        """INSERT INTO network_edges (id, source_id, target_id, edge_type, weight, properties, created_at, updated_at)
           VALUES %s ON CONFLICT (id) DO UPDATE SET
           source_id = EXCLUDED.source_id,
           target_id = EXCLUDED.target_id,
           edge_type = EXCLUDED.edge_type,
           weight = EXCLUDED.weight,
           properties = EXCLUDED.properties,
           updated_at = EXCLUDED.updated_at""",
        data
    )
    
    pg_conn.commit()
    print(f"Migrated {len(data)} network edges")


def migrate_web_content(sqlite_conn, pg_conn):
    """Migrate web_content table"""
    sqlite_cursor = sqlite_conn.cursor()
    pg_cursor = pg_conn.cursor()
    
    sqlite_cursor.execute("SELECT * FROM web_content")
    rows = sqlite_cursor.fetchall()
    
    if not rows:
        print("No web content to migrate")
        return
    
    data = []
    for row in rows:
        metadata = json.loads(row["metadata"]) if row["metadata"] else None
        data.append((
            row["id"],
            row["url"],
            row["content_type"],
            row["content"],
            row["title"],
            json.dumps(metadata) if metadata else None,
            row["fetched_at"],
            row["expires_at"]
        ))
    
    execute_values(
        pg_cursor,
        """INSERT INTO web_content (id, url, content_type, content, title, metadata, fetched_at, expires_at)
           VALUES %s ON CONFLICT (id) DO UPDATE SET
           url = EXCLUDED.url,
           content_type = EXCLUDED.content_type,
           content = EXCLUDED.content,
           title = EXCLUDED.title,
           metadata = EXCLUDED.metadata,
           fetched_at = EXCLUDED.fetched_at,
           expires_at = EXCLUDED.expires_at""",
        data
    )
    
    pg_conn.commit()
    print(f"Migrated {len(data)} web content items")


def migrate_extracted_entities(sqlite_conn, pg_conn):
    """Migrate extracted_entities table"""
    sqlite_cursor = sqlite_conn.cursor()
    pg_cursor = pg_conn.cursor()
    
    sqlite_cursor.execute("SELECT * FROM extracted_entities")
    rows = sqlite_cursor.fetchall()
    
    if not rows:
        print("No extracted entities to migrate")
        return
    
    data = []
    for row in rows:
        properties = json.loads(row["properties"]) if row["properties"] else None
        data.append((
            row["id"],
            row["content_id"],
            row["entity_type"],
            row["entity_text"],
            float(row["confidence"]),
            json.dumps(properties) if properties else None,
            row["created_at"]
        ))
    
    execute_values(
        pg_cursor,
        """INSERT INTO extracted_entities (id, content_id, entity_type, entity_text, confidence, properties, created_at)
           VALUES %s ON CONFLICT (id) DO UPDATE SET
           content_id = EXCLUDED.content_id,
           entity_type = EXCLUDED.entity_type,
           entity_text = EXCLUDED.entity_text,
           confidence = EXCLUDED.confidence,
           properties = EXCLUDED.properties,
           created_at = EXCLUDED.created_at""",
        data
    )
    
    pg_conn.commit()
    print(f"Migrated {len(data)} extracted entities")


def migrate_extracted_relations(sqlite_conn, pg_conn):
    """Migrate extracted_relations table"""
    sqlite_cursor = sqlite_conn.cursor()
    pg_cursor = pg_conn.cursor()
    
    sqlite_cursor.execute("SELECT * FROM extracted_relations")
    rows = sqlite_cursor.fetchall()
    
    if not rows:
        print("No extracted relations to migrate")
        return
    
    data = []
    for row in rows:
        properties = json.loads(row["properties"]) if row["properties"] else None
        data.append((
            row["id"],
            row["content_id"],
            row["source_entity_id"],
            row["target_entity_id"],
            row["relation_type"],
            float(row["confidence"]),
            json.dumps(properties) if properties else None,
            row["created_at"]
        ))
    
    execute_values(
        pg_cursor,
        """INSERT INTO extracted_relations (id, content_id, source_entity_id, target_entity_id, relation_type, confidence, properties, created_at)
           VALUES %s ON CONFLICT (id) DO UPDATE SET
           content_id = EXCLUDED.content_id,
           source_entity_id = EXCLUDED.source_entity_id,
           target_entity_id = EXCLUDED.target_entity_id,
           relation_type = EXCLUDED.relation_type,
           confidence = EXCLUDED.confidence,
           properties = EXCLUDED.properties,
           created_at = EXCLUDED.created_at""",
        data
    )
    
    pg_conn.commit()
    print(f"Migrated {len(data)} extracted relations")


def migrate_agent_discoveries(sqlite_conn, pg_conn):
    """Migrate agent_discoveries table"""
    sqlite_cursor = sqlite_conn.cursor()
    pg_cursor = pg_conn.cursor()
    
    sqlite_cursor.execute("SELECT * FROM agent_discoveries")
    rows = sqlite_cursor.fetchall()
    
    if not rows:
        print("No agent discoveries to migrate")
        return
    
    data = []
    for row in rows:
        discovery_data = json.loads(row["discovery_data"]) if row["discovery_data"] else {}
        data.append((
            row["id"],
            row["agent_id"],
            row["discovery_type"],
            json.dumps(discovery_data),
            row["discovered_at"]
        ))
    
    execute_values(
        pg_cursor,
        """INSERT INTO agent_discoveries (id, agent_id, discovery_type, discovery_data, discovered_at)
           VALUES %s ON CONFLICT (id) DO UPDATE SET
           agent_id = EXCLUDED.agent_id,
           discovery_type = EXCLUDED.discovery_type,
           discovery_data = EXCLUDED.discovery_data,
           discovered_at = EXCLUDED.discovered_at""",
        data
    )
    
    pg_conn.commit()
    print(f"Migrated {len(data)} agent discoveries")


def main():
    parser = argparse.ArgumentParser(description="Migrate SQLite database to PostgreSQL")
    parser.add_argument("--sqlite-path", required=True, help="Path to SQLite database")
    parser.add_argument("--postgres-url", required=True, help="PostgreSQL connection URL (postgres://user:pass@host:port/dbname)")
    
    args = parser.parse_args()
    
    # Connect to SQLite
    sqlite_conn = sqlite3.connect(args.sqlite_path)
    sqlite_conn.row_factory = sqlite3.Row
    
    # Connect to PostgreSQL
    pg_conn = psycopg2.connect(args.postgres_url)
    
    print("Starting migration...")
    
    try:
        # Migrate in order (respecting foreign key constraints)
        migrate_agents(sqlite_conn, pg_conn)
        migrate_semantic_cells(sqlite_conn, pg_conn)
        migrate_couplings(sqlite_conn, pg_conn)
        migrate_network_nodes(sqlite_conn, pg_conn)
        migrate_network_edges(sqlite_conn, pg_conn)
        migrate_web_content(sqlite_conn, pg_conn)
        migrate_extracted_entities(sqlite_conn, pg_conn)
        migrate_extracted_relations(sqlite_conn, pg_conn)
        migrate_agent_discoveries(sqlite_conn, pg_conn)
        
        print("\nMigration completed successfully!")
    except Exception as e:
        print(f"\nMigration failed: {e}")
        pg_conn.rollback()
        raise
    finally:
        sqlite_conn.close()
        pg_conn.close()


if __name__ == "__main__":
    main()
