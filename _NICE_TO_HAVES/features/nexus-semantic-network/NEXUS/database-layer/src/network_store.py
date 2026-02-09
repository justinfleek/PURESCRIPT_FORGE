"""
Nexus Database Layer - Network Store
CRUD operations for network graph nodes and edges
"""

import sqlite3
from typing import List, Optional, Dict, Any
from dataclasses import dataclass
from datetime import datetime
import json


@dataclass
class NetworkNode:
    """Network graph node"""
    id: str
    node_type: str  # agent, concept, entity, content
    label: str
    properties: Dict[str, Any]
    created_at: str
    updated_at: str


@dataclass
class NetworkEdge:
    """Network graph edge"""
    id: str
    source_id: str
    target_id: str
    edge_type: str  # agent-agent, agent-concept, concept-concept, etc.
    weight: float  # 0.0 to 1.0
    properties: Dict[str, Any]
    created_at: str
    updated_at: str


class NetworkStore:
    """
    Network store for CRUD operations on network graph nodes and edges.
    
    Stores social network graph data (nodes and edges).
    """
    
    def __init__(self, conn: sqlite3.Connection):
        """
        Initialize network store.
        
        Args:
            conn: SQLite connection
        """
        self.conn = conn
    
    def save_node(self, node: NetworkNode) -> None:
        """
        Save network node to database.
        
        Args:
            node: Network node to save
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            INSERT OR REPLACE INTO network_nodes (
                id, node_type, label, properties, created_at, updated_at
            ) VALUES (?, ?, ?, ?, ?, ?)
        """, (
            node.id,
            node.node_type,
            node.label,
            json.dumps(node.properties),
            node.created_at,
            node.updated_at
        ))
        self.conn.commit()
    
    def load_node(self, node_id: str) -> Optional[NetworkNode]:
        """
        Load network node from database.
        
        Args:
            node_id: Node ID
            
        Returns:
            Network node or None if not found
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT * FROM network_nodes WHERE id = ?
        """, (node_id,))
        row = cursor.fetchone()
        
        if row is None:
            return None
        
        return NetworkNode(
            id=row["id"],
            node_type=row["node_type"],
            label=row["label"],
            properties=json.loads(row["properties"]),
            created_at=row["created_at"],
            updated_at=row["updated_at"]
        )
    
    def query_nodes(
        self,
        node_type: Optional[str] = None,
        limit: Optional[int] = None
    ) -> List[NetworkNode]:
        """
        Query network nodes, optionally filtered by type.
        
        Args:
            node_type: Optional node type filter
            limit: Optional result limit
            
        Returns:
            List of network nodes
        """
        cursor = self.conn.cursor()
        
        if node_type:
            query = "SELECT * FROM network_nodes WHERE node_type = ? ORDER BY updated_at DESC"
            params = (node_type,)
        else:
            query = "SELECT * FROM network_nodes ORDER BY updated_at DESC"
            params = ()
        
        if limit:
            query += f" LIMIT {limit}"
        
        cursor.execute(query, params)
        rows = cursor.fetchall()
        
        return [
            NetworkNode(
                id=row["id"],
                node_type=row["node_type"],
                label=row["label"],
                properties=json.loads(row["properties"]),
                created_at=row["created_at"],
                updated_at=row["updated_at"]
            )
            for row in rows
        ]
    
    def get_neighbors(self, node_id: str) -> List[NetworkNode]:
        """
        Get neighbor nodes for a given node.
        
        Args:
            node_id: Node ID
            
        Returns:
            List of neighbor nodes
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT n.* FROM network_nodes n
            INNER JOIN network_edges e ON (
                (e.source_id = ? AND e.target_id = n.id) OR
                (e.target_id = ? AND e.source_id = n.id)
            )
            WHERE n.id != ?
        """, (node_id, node_id, node_id))
        rows = cursor.fetchall()
        
        return [
            NetworkNode(
                id=row["id"],
                node_type=row["node_type"],
                label=row["label"],
                properties=json.loads(row["properties"]),
                created_at=row["created_at"],
                updated_at=row["updated_at"]
            )
            for row in rows
        ]
    
    def save_edge(self, edge: NetworkEdge) -> None:
        """
        Save network edge to database.
        
        Args:
            edge: Network edge to save
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            INSERT OR REPLACE INTO network_edges (
                id, source_id, target_id, edge_type,
                weight, properties, created_at, updated_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            edge.id,
            edge.source_id,
            edge.target_id,
            edge.edge_type,
            edge.weight,
            json.dumps(edge.properties),
            edge.created_at,
            edge.updated_at
        ))
        self.conn.commit()
    
    def load_edge(self, edge_id: str) -> Optional[NetworkEdge]:
        """
        Load network edge from database.
        
        Args:
            edge_id: Edge ID
            
        Returns:
            Network edge or None if not found
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT * FROM network_edges WHERE id = ?
        """, (edge_id,))
        row = cursor.fetchone()
        
        if row is None:
            return None
        
        return NetworkEdge(
            id=row["id"],
            source_id=row["source_id"],
            target_id=row["target_id"],
            edge_type=row["edge_type"],
            weight=row["weight"],
            properties=json.loads(row["properties"]),
            created_at=row["created_at"],
            updated_at=row["updated_at"]
        )
    
    def query_edges(
        self,
        source_id: Optional[str] = None,
        target_id: Optional[str] = None,
        edge_type: Optional[str] = None,
        min_weight: Optional[float] = None,
        limit: Optional[int] = None
    ) -> List[NetworkEdge]:
        """
        Query network edges with filters.
        
        Args:
            source_id: Optional source node filter
            target_id: Optional target node filter
            edge_type: Optional edge type filter
            min_weight: Optional minimum weight filter
            limit: Optional result limit
            
        Returns:
            List of network edges
        """
        cursor = self.conn.cursor()
        
        conditions = []
        params = []
        
        if source_id:
            conditions.append("source_id = ?")
            params.append(source_id)
        
        if target_id:
            conditions.append("target_id = ?")
            params.append(target_id)
        
        if edge_type:
            conditions.append("edge_type = ?")
            params.append(edge_type)
        
        if min_weight is not None:
            conditions.append("weight >= ?")
            params.append(min_weight)
        
        where_clause = " AND ".join(conditions) if conditions else "1=1"
        query = f"SELECT * FROM network_edges WHERE {where_clause} ORDER BY weight DESC"
        
        if limit:
            query += f" LIMIT {limit}"
        
        cursor.execute(query, params)
        rows = cursor.fetchall()
        
        return [
            NetworkEdge(
                id=row["id"],
                source_id=row["source_id"],
                target_id=row["target_id"],
                edge_type=row["edge_type"],
                weight=row["weight"],
                properties=json.loads(row["properties"]),
                created_at=row["created_at"],
                updated_at=row["updated_at"]
            )
            for row in rows
        ]
    
    def delete_node(self, node_id: str) -> None:
        """
        Delete network node and its edges.
        
        Args:
            node_id: Node ID
        """
        cursor = self.conn.cursor()
        # Delete edges first
        cursor.execute("DELETE FROM network_edges WHERE source_id = ? OR target_id = ?", (node_id, node_id))
        # Delete node
        cursor.execute("DELETE FROM network_nodes WHERE id = ?", (node_id,))
        self.conn.commit()
    
    def delete_edge(self, edge_id: str) -> None:
        """
        Delete network edge.
        
        Args:
            edge_id: Edge ID
        """
        cursor = self.conn.cursor()
        cursor.execute("DELETE FROM network_edges WHERE id = ?", (edge_id,))
        self.conn.commit()
