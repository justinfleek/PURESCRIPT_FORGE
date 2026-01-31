"""
Nexus Semantic Memory - Create Semantic Cells from Concepts
Create semantic cells from extracted concepts (entities, relations, concepts)
"""

import sys
import json
import argparse
from pathlib import Path
from typing import List, Dict, Any
import uuid

# Import semantic cell types
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "semantic-cells" / "src"))
from core.types import SemanticCell, CellState, CellLevel, BasinType

# Import database layer
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "database-layer" / "src"))
from semantic_store import SemanticStore
from schema import DatabaseConfig, initialize_databases


def create_cells_from_concepts(
    concepts_json: str,
    agent_id: str,
    task_id: str
) -> Dict[str, Any]:
    """
    Create semantic cells from extracted concepts.
    
    Args:
        concepts_json: JSON string containing list of concepts
        agent_id: Agent that discovered the concepts
        task_id: Task that produced the concepts
        
    Returns:
        JSON string with created cells
    """
    try:
        # Parse concepts
        concepts_data = json.loads(concepts_json)
        concepts = concepts_data.get("concepts", [])
        
        # Initialize database
        config = DatabaseConfig(
            sqlite_path="database/semantic.db",
            duckdb_path="database/semantic_analytical.db"
        )
        sqlite_conn, _ = initialize_databases(config)
        store = SemanticStore(sqlite_conn)
        
        created_cells = []
        
        for concept in concepts:
            # Determine cell level based on concept confidence/type
            if concept.get("confidence", 0.5) > 0.8:
                level = CellLevel.COMMON
            elif concept.get("confidence", 0.5) > 0.5:
                level = CellLevel.BASIC
            else:
                level = CellLevel.PRIMITIVE
            
            # Determine basin type
            domain = concept.get("domain", "general")
            basin = BasinType.ENTITY  # Default, could be determined from concept type
            
            # Create cell ID
            cell_id = f"cell_{agent_id}_{task_id}_{uuid.uuid4().hex[:8]}"
            
            # Initialize cell state (512-dim position, all zeros initially)
            # In production, would use embedding model to get actual position
            position = [0.0] * 512
            velocity = [0.0] * 512
            acceleration = [0.0] * 512
            spin = [0.0, 0.0, 0.0]
            grade = concept.get("confidence", 0.5)
            energy = 0.5  # Initial energy
            
            state = CellState(
                position=position,
                velocity=velocity,
                acceleration=acceleration,
                spin=spin,
                grade=grade,
                energy=energy
            )
            
            # Create semantic cell
            cell = SemanticCell(
                id=cell_id,
                name=concept.get("name", concept.get("text", "unknown")),
                description=concept.get("description", ""),
                level=level,
                domain=domain,
                basin=basin,
                state=state,
                parent_id=None,
                children_ids=[],
                coupling_ids=[]
            )
            
            # Save to database
            store.save_cell(cell)
            
            created_cells.append({
                "cellId": cell_id,
                "name": cell.name,
                "level": level.value,
                "domain": domain,
                "basin": basin.value
            })
        
        sqlite_conn.close()
        
        return {
            "success": True,
            "cellsCreated": len(created_cells),
            "cells": created_cells,
            "agentId": agent_id,
            "taskId": task_id
        }
    except Exception as e:
        return {
            "success": False,
            "error": str(e),
            "cellsCreated": 0,
            "cells": []
        }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Create semantic cells from concepts")
    parser.add_argument("--concepts", required=True, help="JSON string with concepts")
    parser.add_argument("--agent-id", required=True, help="Agent ID")
    parser.add_argument("--task-id", required=True, help="Task ID")
    
    args = parser.parse_args()
    
    result = create_cells_from_concepts(
        args.concepts,
        args.agent_id,
        args.task_id
    )
    
    print(json.dumps(result))
