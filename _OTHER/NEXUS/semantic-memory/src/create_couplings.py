"""
Nexus Semantic Memory - Create Couplings from Relations
Create couplings between semantic cells from extracted relations
"""

import sys
import json
import argparse
from pathlib import Path
from typing import List, Dict, Any
import uuid

# Import semantic cell types
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "semantic-cells" / "src"))
from core.types import Coupling, CouplingType

# Import database layer
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "database-layer" / "src"))
from semantic_store import SemanticStore
from schema import DatabaseConfig, initialize_databases


def create_couplings_from_relations(
    relations_json: str,
    cell_map_json: str
) -> Dict[str, Any]:
    """
    Create couplings from extracted relations.
    
    Args:
        relations_json: JSON string containing list of relations
        cell_map_json: JSON string mapping concept IDs to semantic cell IDs
        
    Returns:
        JSON string with created couplings
    """
    try:
        # Parse relations and cell map
        relations_data = json.loads(relations_json)
        relations = relations_data.get("relations", [])
        
        cell_map_data = json.loads(cell_map_json)
        cell_map = cell_map_data.get("cellMap", {})
        
        # Initialize database
        config = DatabaseConfig(
            sqlite_path="database/semantic.db",
            duckdb_path="database/semantic_analytical.db"
        )
        sqlite_conn, _ = initialize_databases(config)
        store = SemanticStore(sqlite_conn)
        
        created_couplings = []
        
        # Map relation types to coupling types
        relation_type_map = {
            "works_at": CouplingType.FUNCTIONAL,
            "located_in": CouplingType.NEAR,
            "founded_by": CouplingType.CAUSES,
            "co_occurrence": CouplingType.SIMILAR,
            "is_a": CouplingType.IS_A,
            "has": CouplingType.HAS,
            "part_of": CouplingType.PART_OF,
            "contains": CouplingType.CONTAINS
        }
        
        for relation in relations:
            source_concept_id = relation.get("source_entity_id") or relation.get("sourceEntityId")
            target_concept_id = relation.get("target_entity_id") or relation.get("targetEntityId")
            relation_type = relation.get("relation_type") or relation.get("relationType", "co_occurrence")
            
            # Map to semantic cell IDs
            source_cell_id = cell_map.get(source_concept_id)
            target_cell_id = cell_map.get(target_concept_id)
            
            if not source_cell_id or not target_cell_id:
                continue  # Skip if cells don't exist
            
            # Get coupling type
            coupling_type = relation_type_map.get(relation_type, CouplingType.SIMILAR)
            
            # Calculate strength from confidence
            strength = relation.get("confidence", 0.5)
            strength = max(0.0, min(1.0, strength))  # Clamp to [0, 1]
            
            # Create coupling ID
            coupling_id = f"coupling_{uuid.uuid4().hex[:8]}"
            
            # Create coupling
            coupling = Coupling(
                id=coupling_id,
                source_id=source_cell_id,
                target_id=target_cell_id,
                coupling_type=coupling_type,
                strength=strength,
                bidirectional=False  # Default to unidirectional
            )
            
            # Save to database
            store.save_coupling(coupling)
            
            created_couplings.append({
                "couplingId": coupling_id,
                "sourceCellId": source_cell_id,
                "targetCellId": target_cell_id,
                "couplingType": coupling_type.value,
                "strength": strength
            })
        
        sqlite_conn.close()
        
        return {
            "success": True,
            "couplingsCreated": len(created_couplings),
            "couplings": created_couplings
        }
    except Exception as e:
        return {
            "success": False,
            "error": str(e),
            "couplingsCreated": 0,
            "couplings": []
        }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Create couplings from relations")
    parser.add_argument("--relations", required=True, help="JSON string with relations")
    parser.add_argument("--cell-map", required=True, help="JSON string mapping concept IDs to cell IDs")
    
    args = parser.parse_args()
    
    result = create_couplings_from_relations(
        args.relations,
        getattr(args, "cell-map")
    )
    
    print(json.dumps(result))
