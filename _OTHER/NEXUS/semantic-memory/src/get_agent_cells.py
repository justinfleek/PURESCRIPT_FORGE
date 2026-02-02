"""
Nexus Semantic Memory - Get Agent Semantic Cells
Get semantic cells associated with an agent (cells created/updated by agent)
"""

import sys
import json
import argparse
from pathlib import Path
from typing import List, Dict, Any

# Import database layer
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "database-layer" / "src"))
from semantic_store import SemanticStore
from schema import DatabaseConfig, initialize_databases


def get_agent_semantic_cells(agent_id: str) -> Dict[str, Any]:
    """
    Get semantic cells associated with an agent.
    
    Args:
        agent_id: Agent ID
        
    Returns:
        JSON string with agent's semantic cells
    """
    try:
        # Initialize database
        config = DatabaseConfig(
            sqlite_path="database/semantic.db",
            duckdb_path="database/semantic_analytical.db"
        )
        sqlite_conn, _ = initialize_databases(config)
        store = SemanticStore(sqlite_conn)
        
        # Query cells created by this agent (cells with agent ID in cell ID prefix)
        # In production, would have agent_id column in semantic_cells table
        all_cells = store.query_cells(limit=1000)  # Get all cells (would filter by agent_id in production)
        
        # Filter cells created by this agent (check cell ID prefix)
        agent_cells = [
            cell for cell in all_cells
            if cell.id.startswith(f"cell_{agent_id}_")
        ]
        
        # Sort by energy (highest first) to get primary cell
        agent_cells.sort(key=lambda c: c.state.energy, reverse=True)
        
        # Convert to JSON-serializable format
        cells_data = []
        for cell in agent_cells:
            cells_data.append({
                "cellId": cell.id,
                "name": cell.name,
                "description": cell.description,
                "level": cell.level.value,
                "domain": cell.domain,
                "basin": cell.basin.value,
                "state": {
                    "position": cell.state.position[:3],  # First 3 dims for avatar
                    "energy": cell.state.energy,
                    "grade": cell.state.grade,
                    "spin": cell.state.spin
                },
                "energy": cell.state.energy,  # For sorting/selection
                "grade": cell.state.grade
            })
        
        # Get primary cell (highest energy)
        primary_cell = cells_data[0] if cells_data else None
        
        sqlite_conn.close()
        
        return {
            "success": True,
            "agentId": agent_id,
            "cellsCount": len(cells_data),
            "cells": cells_data,
            "primaryCell": primary_cell
        }
    except Exception as e:
        return {
            "success": False,
            "error": str(e),
            "agentId": agent_id,
            "cellsCount": 0,
            "cells": [],
            "primaryCell": None
        }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Get agent semantic cells")
    parser.add_argument("--agent-id", required=True, help="Agent ID")
    
    args = parser.parse_args()
    
    result = get_agent_semantic_cells(args.agent_id)
    
    print(json.dumps(result))
