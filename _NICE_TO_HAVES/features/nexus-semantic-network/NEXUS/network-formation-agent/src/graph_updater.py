"""
Nexus Network Formation Agent - Graph Updater
Update network graph with new nodes/edges
"""

from typing import List
import sys
from pathlib import Path

# Import network graph types
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "network-graph" / "src"))
from graph import NetworkGraph, Node, Edge, NodeType

# Import connection types
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "network-formation-agent" / "src"))
from connection_discoverer import Connection
from edge_builder import EdgeBuilder
from weight_calculator import WeightCalculator


class GraphUpdater:
    """
    Graph updater for updating network graph with new nodes/edges.
    
    Handles:
    - Adding new nodes
    - Adding/updating edges
    - Merging duplicate nodes
    - Updating edge weights
    """
    
    def __init__(self, graph: NetworkGraph):
        """
        Initialize graph updater.
        
        Args:
            graph: Network graph
        """
        self.graph = graph
        self.edge_builder = EdgeBuilder(graph)
        self.weight_calculator = WeightCalculator()
    
    def update_graph(
        self,
        nodes: List[Node],
        edges: List[Edge]
    ) -> None:
        """
        Update graph with new nodes and edges.
        
        Args:
            nodes: List of nodes to add/update
            edges: List of edges to add/update
        """
        # Add/update nodes
        for node in nodes:
            existing_node = self.graph.get_node(node.id)
            if existing_node:
                # Update existing node properties
                existing_node.properties.update(node.properties)
            else:
                # Add new node
                self.graph.add_node(node)
        
        # Add/update edges
        for edge in edges:
            existing_edge = self.graph.get_edge(edge.id)
            if existing_edge:
                # Update edge weight (weighted average)
                new_weight = 0.7 * edge.weight + 0.3 * existing_edge.weight
                existing_edge.weight = new_weight
                existing_edge.properties.update(edge.properties)
            else:
                # Add new edge
                self.graph.add_edge(edge)
    
    def update_from_connections(
        self,
        connections: List[Connection]
    ) -> None:
        """
        Update graph from discovered connections.
        
        Args:
            connections: List of connections
        """
        # Build edges from connections
        edges = self.edge_builder.build_edges_from_connections(connections)
        
        # Update graph with edges
        for edge in edges:
            existing_edge = self.graph.get_edge(edge.id)
            if existing_edge:
                # Update weight
                from weight_calculator import Evidence
                evidence = [
                    Evidence(
                        source=conn.connection_type,
                        strength=conn.strength,
                        timestamp=""
                    )
                    for conn in connections
                    if conn.source_id == edge.source_id and conn.target_id == edge.target_id
                ]
                new_weight = self.weight_calculator.calculate_weight(existing_edge, evidence)
                existing_edge.weight = new_weight
            else:
                # Add new edge
                self.graph.add_edge(edge)
