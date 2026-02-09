"""
Nexus Database Layer - Semantic Store
CRUD operations for semantic cells and couplings
"""

import sqlite3
from typing import List, Optional, Dict, Any
from dataclasses import dataclass
from datetime import datetime
import json

# Import semantic cell types
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "semantic-cells" / "src"))
from core.types import SemanticCell, Coupling, CellLevel, BasinType, CouplingType


class SemanticStore:
    """
    Semantic store for CRUD operations on semantic cells and couplings.
    
    Stores semantic cells (concepts) and couplings (relationships).
    """
    
    def __init__(self, conn: sqlite3.Connection):
        """
        Initialize semantic store.
        
        Args:
            conn: SQLite connection
        """
        self.conn = conn
    
    def save_cell(self, cell: SemanticCell) -> None:
        """
        Save semantic cell to database.
        
        Args:
            cell: Semantic cell to save
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            INSERT OR REPLACE INTO semantic_cells (
                id, name, description, level, domain, basin,
                state, parent_id, children_ids, coupling_ids,
                created_at, updated_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            cell.id,
            cell.name,
            cell.description,
            cell.level.value,
            cell.domain,
            cell.basin.value,
            json.dumps({
                "position": cell.state.position,
                "velocity": cell.state.velocity,
                "acceleration": cell.state.acceleration,
                "spin": cell.state.spin,
                "grade": cell.state.grade,
                "energy": cell.state.energy
            }),
            cell.parent_id,
            json.dumps(cell.children_ids),
            json.dumps(cell.coupling_ids),
            datetime.utcnow().isoformat(),
            datetime.utcnow().isoformat()
        ))
        self.conn.commit()
    
    def load_cell(self, cell_id: str) -> Optional[SemanticCell]:
        """
        Load semantic cell from database.
        
        Args:
            cell_id: Cell ID
            
        Returns:
            Semantic cell or None if not found
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT * FROM semantic_cells WHERE id = ?
        """, (cell_id,))
        row = cursor.fetchone()
        
        if row is None:
            return None
        
        # Reconstruct CellState
        state_dict = json.loads(row["state"])
        from core.types import CellState
        state = CellState(
            position=state_dict["position"],
            velocity=state_dict["velocity"],
            acceleration=state_dict["acceleration"],
            spin=state_dict["spin"],
            grade=state_dict["grade"],
            energy=state_dict["energy"]
        )
        
        return SemanticCell(
            id=row["id"],
            name=row["name"],
            description=row["description"],
            level=CellLevel(row["level"]),
            domain=row["domain"],
            basin=BasinType(row["basin"]),
            state=state,
            parent_id=row["parent_id"],
            children_ids=json.loads(row["children_ids"]),
            coupling_ids=json.loads(row["coupling_ids"])
        )
    
    def update_cell_state(self, cell_id: str, state) -> None:
        """
        Update cell state.
        
        Args:
            cell_id: Cell ID
            state: CellState object
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            UPDATE semantic_cells
            SET state = ?, updated_at = ?
            WHERE id = ?
        """, (
            json.dumps({
                "position": state.position,
                "velocity": state.velocity,
                "acceleration": state.acceleration,
                "spin": state.spin,
                "grade": state.grade,
                "energy": state.energy
            }),
            datetime.utcnow().isoformat(),
            cell_id
        ))
        self.conn.commit()
    
    def query_cells(
        self,
        level: Optional[CellLevel] = None,
        domain: Optional[str] = None,
        basin: Optional[BasinType] = None,
        min_energy: Optional[float] = None,
        max_energy: Optional[float] = None,
        limit: Optional[int] = None
    ) -> List[SemanticCell]:
        """
        Query semantic cells with filters.
        
        Args:
            level: Optional level filter
            domain: Optional domain filter
            basin: Optional basin filter
            min_energy: Optional minimum energy filter
            max_energy: Optional maximum energy filter
            limit: Optional result limit
            
        Returns:
            List of semantic cells matching filters
        """
        cursor = self.conn.cursor()
        
        # Build query dynamically
        conditions = []
        params = []
        
        if level:
            conditions.append("level = ?")
            params.append(level.value)
        
        if domain:
            conditions.append("domain = ?")
            params.append(domain)
        
        if basin:
            conditions.append("basin = ?")
            params.append(basin.value)
        
        if min_energy is not None or max_energy is not None:
            # Need to parse JSON state to filter by energy
            # For now, load all and filter in Python
            # In production, would use JSON extraction
            pass
        
        where_clause = " AND ".join(conditions) if conditions else "1=1"
        query = f"SELECT * FROM semantic_cells WHERE {where_clause} ORDER BY updated_at DESC"
        
        if limit:
            query += f" LIMIT {limit}"
        
        cursor.execute(query, params)
        rows = cursor.fetchall()
        
        cells = []
        for row in rows:
            # Reconstruct CellState
            state_dict = json.loads(row["state"])
            from core.types import CellState
            state = CellState(
                position=state_dict["position"],
                velocity=state_dict["velocity"],
                acceleration=state_dict["acceleration"],
                spin=state_dict["spin"],
                grade=state_dict["grade"],
                energy=state_dict["energy"]
            )
            
            # Filter by energy if needed
            if min_energy is not None and state.energy < min_energy:
                continue
            if max_energy is not None and state.energy > max_energy:
                continue
            
            cells.append(SemanticCell(
                id=row["id"],
                name=row["name"],
                description=row["description"],
                level=CellLevel(row["level"]),
                domain=row["domain"],
                basin=BasinType(row["basin"]),
                state=state,
                parent_id=row["parent_id"],
                children_ids=json.loads(row["children_ids"]),
                coupling_ids=json.loads(row["coupling_ids"])
            ))
        
        return cells
    
    def save_coupling(self, coupling: Coupling) -> None:
        """
        Save coupling to database.
        
        Args:
            coupling: Coupling to save
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            INSERT OR REPLACE INTO couplings (
                id, source_id, target_id, coupling_type,
                strength, bidirectional, created_at, updated_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            coupling.id,
            coupling.source_id,
            coupling.target_id,
            coupling.coupling_type.value,
            coupling.strength,
            1 if coupling.bidirectional else 0,
            datetime.utcnow().isoformat(),
            datetime.utcnow().isoformat()
        ))
        self.conn.commit()
    
    def load_coupling(self, coupling_id: str) -> Optional[Coupling]:
        """
        Load coupling from database.
        
        Args:
            coupling_id: Coupling ID
            
        Returns:
            Coupling or None if not found
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT * FROM couplings WHERE id = ?
        """, (coupling_id,))
        row = cursor.fetchone()
        
        if row is None:
            return None
        
        return Coupling(
            id=row["id"],
            source_id=row["source_id"],
            target_id=row["target_id"],
            coupling_type=CouplingType(row["coupling_type"]),
            strength=row["strength"],
            bidirectional=bool(row["bidirectional"])
        )
    
    def load_couplings(self, cell_id: str) -> List[Coupling]:
        """
        Load all couplings for a cell (as source or target).
        
        Args:
            cell_id: Cell ID
            
        Returns:
            List of couplings
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT * FROM couplings
            WHERE source_id = ? OR target_id = ?
            ORDER BY strength DESC
        """, (cell_id, cell_id))
        rows = cursor.fetchall()
        
        return [
            Coupling(
                id=row["id"],
                source_id=row["source_id"],
                target_id=row["target_id"],
                coupling_type=CouplingType(row["coupling_type"]),
                strength=row["strength"],
                bidirectional=bool(row["bidirectional"])
            )
            for row in rows
        ]
    
    def query_by_coupling_type(self, coupling_type: CouplingType) -> List[Coupling]:
        """
        Query couplings by type.
        
        Args:
            coupling_type: Coupling type
            
        Returns:
            List of couplings
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT * FROM couplings
            WHERE coupling_type = ?
            ORDER BY strength DESC
        """, (coupling_type.value,))
        rows = cursor.fetchall()
        
        return [
            Coupling(
                id=row["id"],
                source_id=row["source_id"],
                target_id=row["target_id"],
                coupling_type=CouplingType(row["coupling_type"]),
                strength=row["strength"],
                bidirectional=bool(row["bidirectional"])
            )
            for row in rows
        ]
    
    def delete_cell(self, cell_id: str) -> None:
        """
        Delete semantic cell and its couplings.
        
        Args:
            cell_id: Cell ID
        """
        cursor = self.conn.cursor()
        # Delete couplings first (foreign key constraint)
        cursor.execute("DELETE FROM couplings WHERE source_id = ? OR target_id = ?", (cell_id, cell_id))
        # Delete cell
        cursor.execute("DELETE FROM semantic_cells WHERE id = ?", (cell_id,))
        self.conn.commit()
    
    def delete_coupling(self, coupling_id: str) -> None:
        """
        Delete coupling.
        
        Args:
            coupling_id: Coupling ID
        """
        cursor = self.conn.cursor()
        cursor.execute("DELETE FROM couplings WHERE id = ?", (coupling_id,))
        self.conn.commit()
