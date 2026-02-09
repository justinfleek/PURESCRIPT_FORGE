"""
Nexus Network Graph
Graph data structure for social networks (nodes, edges, weights)
"""

from typing import List, Dict, Set, Optional, Tuple
from dataclasses import dataclass, field
from enum import Enum
from collections import defaultdict
import json


class NodeType(Enum):
    """Network node type"""
    AGENT = "agent"
    CONCEPT = "concept"
    ENTITY = "entity"
    CONTENT = "content"


class EdgeType(Enum):
    """Network edge type"""
    AGENT_AGENT = "agent-agent"
    AGENT_CONCEPT = "agent-concept"
    CONCEPT_CONCEPT = "concept-concept"
    ENTITY_ENTITY = "entity-entity"
    CONTENT_CONCEPT = "content-concept"


@dataclass
class Node:
    """Network graph node"""
    id: str
    node_type: NodeType
    label: str
    properties: Dict[str, any] = field(default_factory=dict)
    
    def __hash__(self):
        return hash(self.id)
    
    def __eq__(self, other):
        return isinstance(other, Node) and self.id == other.id


@dataclass
class Edge:
    """Network graph edge"""
    id: str
    source_id: str
    target_id: str
    edge_type: EdgeType
    weight: float  # 0.0 to 1.0
    properties: Dict[str, any] = field(default_factory=dict)
    
    def __hash__(self):
        return hash((self.source_id, self.target_id, self.edge_type))
    
    def __eq__(self, other):
        return (
            isinstance(other, Edge) and
            self.source_id == other.source_id and
            self.target_id == other.target_id and
            self.edge_type == other.edge_type
        )


@dataclass
class Community:
    """Network community (cluster of nodes)"""
    id: str
    node_ids: List[str]
    properties: Dict[str, any] = field(default_factory=dict)


class NetworkGraph:
    """
    Network graph data structure for social networks.
    
    Represents a graph with nodes (agents, concepts, entities, content) and
    edges (relationships, interactions, discoveries).
    """
    
    def __init__(self):
        """Initialize empty network graph"""
        self.nodes: Dict[str, Node] = {}
        self.edges: Dict[str, Edge] = {}
        self.adjacency: Dict[str, Set[str]] = defaultdict(set)  # node_id -> set of neighbor node_ids
        self.edge_index: Dict[Tuple[str, str], List[str]] = defaultdict(list)  # (source, target) -> list of edge_ids
    
    def add_node(self, node: Node) -> None:
        """
        Add node to graph.
        
        Args:
            node: Node to add
        """
        self.nodes[node.id] = node
        if node.id not in self.adjacency:
            self.adjacency[node.id] = set()
    
    def remove_node(self, node_id: str) -> None:
        """
        Remove node and its edges from graph.
        
        Args:
            node_id: Node ID
        """
        if node_id not in self.nodes:
            return
        
        # Remove all edges connected to this node
        neighbor_ids = list(self.adjacency[node_id])
        for neighbor_id in neighbor_ids:
            self.remove_edge_by_nodes(node_id, neighbor_id)
        
        # Remove node
        del self.nodes[node_id]
        del self.adjacency[node_id]
    
    def get_node(self, node_id: str) -> Optional[Node]:
        """
        Get node by ID.
        
        Args:
            node_id: Node ID
            
        Returns:
            Node or None if not found
        """
        return self.nodes.get(node_id)
    
    def add_edge(self, edge: Edge) -> None:
        """
        Add edge to graph.
        
        Args:
            edge: Edge to add
        """
        # Validate nodes exist
        if edge.source_id not in self.nodes:
            raise ValueError(f"Source node {edge.source_id} not found")
        if edge.target_id not in self.nodes:
            raise ValueError(f"Target node {edge.target_id} not found")
        
        # Validate weight
        if not (0.0 <= edge.weight <= 1.0):
            raise ValueError(f"Edge weight must be in [0.0, 1.0], got {edge.weight}")
        
        # Add edge
        self.edges[edge.id] = edge
        
        # Update adjacency
        self.adjacency[edge.source_id].add(edge.target_id)
        self.adjacency[edge.target_id].add(edge.source_id)
        
        # Update edge index
        self.edge_index[(edge.source_id, edge.target_id)].append(edge.id)
    
    def remove_edge(self, edge_id: str) -> None:
        """
        Remove edge from graph.
        
        Args:
            edge_id: Edge ID
        """
        if edge_id not in self.edges:
            return
        
        edge = self.edges[edge_id]
        
        # Remove from adjacency
        self.adjacency[edge.source_id].discard(edge.target_id)
        self.adjacency[edge.target_id].discard(edge.source_id)
        
        # Remove from edge index
        edge_key = (edge.source_id, edge.target_id)
        if edge_key in self.edge_index:
            self.edge_index[edge_key].remove(edge_id)
            if not self.edge_index[edge_key]:
                del self.edge_index[edge_key]
        
        # Remove edge
        del self.edges[edge_id]
    
    def remove_edge_by_nodes(self, source_id: str, target_id: str) -> None:
        """
        Remove all edges between two nodes.
        
        Args:
            source_id: Source node ID
            target_id: Target node ID
        """
        edge_key = (source_id, target_id)
        if edge_key in self.edge_index:
            edge_ids = list(self.edge_index[edge_key])
            for edge_id in edge_ids:
                self.remove_edge(edge_id)
    
    def get_edge(self, edge_id: str) -> Optional[Edge]:
        """
        Get edge by ID.
        
        Args:
            edge_id: Edge ID
            
        Returns:
            Edge or None if not found
        """
        return self.edges.get(edge_id)
    
    def get_neighbors(self, node_id: str) -> List[Node]:
        """
        Get neighbor nodes for a node.
        
        Args:
            node_id: Node ID
            
        Returns:
            List of neighbor nodes
        """
        if node_id not in self.adjacency:
            return []
        
        neighbor_ids = self.adjacency[node_id]
        return [self.nodes[nid] for nid in neighbor_ids if nid in self.nodes]
    
    def get_edges(self, source_id: Optional[str] = None, target_id: Optional[str] = None) -> List[Edge]:
        """
        Get edges, optionally filtered by source or target.
        
        Args:
            source_id: Optional source node filter
            target_id: Optional target node filter
            
        Returns:
            List of edges
        """
        if source_id and target_id:
            edge_key = (source_id, target_id)
            if edge_key in self.edge_index:
                return [self.edges[eid] for eid in self.edge_index[edge_key] if eid in self.edges]
            return []
        elif source_id:
            return [edge for edge in self.edges.values() if edge.source_id == source_id]
        elif target_id:
            return [edge for edge in self.edges.values() if edge.target_id == target_id]
        else:
            return list(self.edges.values())
    
    def get_nodes_by_type(self, node_type: NodeType) -> List[Node]:
        """
        Get all nodes of a given type.
        
        Args:
            node_type: Node type
            
        Returns:
            List of nodes
        """
        return [node for node in self.nodes.values() if node.node_type == node_type]
    
    def get_edges_by_type(self, edge_type: EdgeType) -> List[Edge]:
        """
        Get all edges of a given type.
        
        Args:
            edge_type: Edge type
            
        Returns:
            List of edges
        """
        return [edge for edge in self.edges.values() if edge.edge_type == edge_type]
    
    def node_count(self) -> int:
        """Get total number of nodes"""
        return len(self.nodes)
    
    def edge_count(self) -> int:
        """Get total number of edges"""
        return len(self.edges)
    
    def to_dict(self) -> Dict:
        """
        Convert graph to dictionary (for serialization).
        
        Returns:
            Dictionary representation
        """
        return {
            "nodes": [
                {
                    "id": node.id,
                    "node_type": node.node_type.value,
                    "label": node.label,
                    "properties": node.properties
                }
                for node in self.nodes.values()
            ],
            "edges": [
                {
                    "id": edge.id,
                    "source_id": edge.source_id,
                    "target_id": edge.target_id,
                    "edge_type": edge.edge_type.value,
                    "weight": edge.weight,
                    "properties": edge.properties
                }
                for edge in self.edges.values()
            ]
        }
    
    @classmethod
    def from_dict(cls, data: Dict) -> "NetworkGraph":
        """
        Create graph from dictionary.
        
        Args:
            data: Dictionary representation
            
        Returns:
            NetworkGraph instance
        """
        graph = cls()
        
        # Add nodes
        for node_data in data.get("nodes", []):
            node = Node(
                id=node_data["id"],
                node_type=NodeType(node_data["node_type"]),
                label=node_data["label"],
                properties=node_data.get("properties", {})
            )
            graph.add_node(node)
        
        # Add edges
        for edge_data in data.get("edges", []):
            edge = Edge(
                id=edge_data["id"],
                source_id=edge_data["source_id"],
                target_id=edge_data["target_id"],
                edge_type=EdgeType(edge_data["edge_type"]),
                weight=edge_data["weight"],
                properties=edge_data.get("properties", {})
            )
            graph.add_edge(edge)
        
        return graph
