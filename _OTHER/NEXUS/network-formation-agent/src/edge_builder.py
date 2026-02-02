"""
Nexus Network Formation Agent - Edge Builder
Build edges in network graph
"""

from typing import List
import sys
from pathlib import Path

# Import network graph types
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "network-graph" / "src"))
from graph import NetworkGraph, Node, Edge, NodeType, EdgeType

# Import connection types
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "network-formation-agent" / "src"))
from connection_discoverer import Connection


class EdgeBuilder:
    """
    Edge builder for building edges in network graph.
    
    Converts discovered connections into network graph edges.
    """
    
    def __init__(self, graph: NetworkGraph):
        """
        Initialize edge builder.
        
        Args:
            graph: Network graph
        """
        self.graph = graph
    
    def build_edge(
        self,
        source: Node,
        target: Node,
        connection: Connection
    ) -> Edge:
        """
        Build edge from connection.
        
        Args:
            source: Source node
            target: Target node
            connection: Discovered connection
            
        Returns:
            Network edge
        """
        # Determine edge type from connection type and node types
        edge_type = self._determine_edge_type(source, target, connection)
        
        # Create edge
        edge_id = f"edge_{source.id}_{target.id}_{connection.connection_type}"
        
        edge = Edge(
            id=edge_id,
            source_id=source.id,
            target_id=target.id,
            edge_type=edge_type,
            weight=connection.strength,
            properties={
                "connection_type": connection.connection_type,
                "evidence": connection.evidence,
                **(connection.properties or {})
            }
        )
        
        return edge
    
    def build_edges_from_connections(
        self,
        connections: List[Connection]
    ) -> List[Edge]:
        """
        Build multiple edges from connections.
        
        Args:
            connections: List of connections
            
        Returns:
            List of network edges
        """
        edges = []
        
        for connection in connections:
            # Get source and target nodes
            source = self.graph.get_node(connection.source_id)
            target = self.graph.get_node(connection.target_id)
            
            if source is None or target is None:
                continue  # Skip if nodes don't exist
            
            # Build edge
            edge = self.build_edge(source, target, connection)
            edges.append(edge)
        
        return edges
    
    def _determine_edge_type(
        self,
        source: Node,
        target: Node,
        connection: Connection
    ) -> EdgeType:
        """
        Determine edge type from node types and connection.
        
        Args:
            source: Source node
            target: Target node
            connection: Connection
            
        Returns:
            Edge type
        """
        # Map node type combinations to edge types
        if source.node_type == NodeType.AGENT and target.node_type == NodeType.AGENT:
            return EdgeType.AGENT_AGENT
        elif source.node_type == NodeType.AGENT and target.node_type == NodeType.CONCEPT:
            return EdgeType.AGENT_CONCEPT
        elif source.node_type == NodeType.CONCEPT and target.node_type == NodeType.CONCEPT:
            return EdgeType.CONCEPT_CONCEPT
        elif source.node_type == NodeType.ENTITY and target.node_type == NodeType.ENTITY:
            return EdgeType.ENTITY_ENTITY
        elif source.node_type == NodeType.CONTENT and target.node_type == NodeType.CONCEPT:
            return EdgeType.CONTENT_CONCEPT
        else:
            # Default to concept-concept for unknown combinations
            return EdgeType.CONCEPT_CONCEPT
