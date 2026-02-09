"""
Nexus Network Graph - Metrics
Calculate network metrics (centrality, clustering, etc.)
"""

from typing import List, Dict, Set
from collections import defaultdict, deque
from .graph import NetworkGraph, Node, Edge


class NetworkMetrics:
    """
    Network metrics calculator for network graphs.
    
    Calculates various network metrics:
    - Centrality (degree, betweenness, closeness)
    - Clustering coefficient
    - Community detection
    - Path lengths
    """
    
    def __init__(self, graph: NetworkGraph):
        """
        Initialize metrics calculator.
        
        Args:
            graph: Network graph
        """
        self.graph = graph
    
    def degree_centrality(self, node_id: str) -> float:
        """
        Calculate degree centrality for a node.
        
        Degree centrality = number of neighbors / (total nodes - 1)
        
        Args:
            node_id: Node ID
            
        Returns:
            Degree centrality (0.0 to 1.0)
        """
        if node_id not in self.graph.nodes:
            return 0.0
        
        neighbor_count = len(self.graph.adjacency[node_id])
        total_nodes = self.graph.node_count()
        
        if total_nodes <= 1:
            return 0.0
        
        return neighbor_count / (total_nodes - 1)
    
    def betweenness_centrality(self, node_id: str) -> float:
        """
        Calculate betweenness centrality for a node.
        
        Betweenness centrality = fraction of shortest paths that pass through node
        
        Args:
            node_id: Node ID
            
        Returns:
            Betweenness centrality (0.0 to 1.0)
        """
        if node_id not in self.graph.nodes:
            return 0.0
        
        # Calculate shortest paths between all pairs
        all_nodes = list(self.graph.nodes.keys())
        total_paths = 0
        paths_through_node = 0
        
        for source in all_nodes:
            if source == node_id:
                continue
            for target in all_nodes:
                if target == node_id or target == source:
                    continue
                
                # Find shortest path
                path = self._shortest_path(source, target)
                if path:
                    total_paths += 1
                    if node_id in path[1:-1]:  # Not start or end
                        paths_through_node += 1
        
        if total_paths == 0:
            return 0.0
        
        return paths_through_node / total_paths
    
    def closeness_centrality(self, node_id: str) -> float:
        """
        Calculate closeness centrality for a node.
        
        Closeness centrality = 1 / average distance to all other nodes
        
        Args:
            node_id: Node ID
            
        Returns:
            Closeness centrality (0.0 to 1.0)
        """
        if node_id not in self.graph.nodes:
            return 0.0
        
        # Calculate distances to all other nodes
        distances = self._distances_from_node(node_id)
        
        if not distances:
            return 0.0
        
        # Average distance
        avg_distance = sum(distances.values()) / len(distances)
        
        if avg_distance == 0:
            return 1.0
        
        # Normalize (inverse of average distance, scaled to [0, 1])
        # For a connected graph, max distance is (n-1), so normalize by that
        max_possible_distance = self.graph.node_count() - 1
        if max_possible_distance == 0:
            return 1.0
        
        normalized_distance = avg_distance / max_possible_distance
        return 1.0 - normalized_distance
    
    def clustering_coefficient(self, node_id: str) -> float:
        """
        Calculate clustering coefficient for a node.
        
        Clustering coefficient = actual edges between neighbors / possible edges
        
        Args:
            node_id: Node ID
            
        Returns:
            Clustering coefficient (0.0 to 1.0)
        """
        if node_id not in self.graph.nodes:
            return 0.0
        
        neighbors = list(self.graph.adjacency[node_id])
        
        if len(neighbors) < 2:
            return 0.0
        
        # Count edges between neighbors
        edges_between_neighbors = 0
        for i, neighbor1 in enumerate(neighbors):
            for neighbor2 in neighbors[i+1:]:
                if neighbor2 in self.graph.adjacency[neighbor1]:
                    edges_between_neighbors += 1
        
        # Possible edges between neighbors = n * (n-1) / 2
        possible_edges = len(neighbors) * (len(neighbors) - 1) / 2
        
        if possible_edges == 0:
            return 0.0
        
        return edges_between_neighbors / possible_edges
    
    def average_clustering_coefficient(self) -> float:
        """
        Calculate average clustering coefficient for entire graph.
        
        Returns:
            Average clustering coefficient (0.0 to 1.0)
        """
        if self.graph.node_count() == 0:
            return 0.0
        
        coefficients = [
            self.clustering_coefficient(node_id)
            for node_id in self.graph.nodes.keys()
        ]
        
        return sum(coefficients) / len(coefficients)
    
    def detect_communities(self) -> List[List[str]]:
        """
        Detect communities in network using simple connected components.
        
        More sophisticated algorithms (Louvain, Leiden) would be used in production.
        
        Returns:
            List of communities (each community is a list of node IDs)
        """
        visited: Set[str] = set()
        communities: List[List[str]] = []
        
        for node_id in self.graph.nodes.keys():
            if node_id in visited:
                continue
            
            # BFS to find connected component
            community = []
            queue = deque([node_id])
            visited.add(node_id)
            
            while queue:
                current = queue.popleft()
                community.append(current)
                
                for neighbor_id in self.graph.adjacency[current]:
                    if neighbor_id not in visited:
                        visited.add(neighbor_id)
                        queue.append(neighbor_id)
            
            if community:
                communities.append(community)
        
        return communities
    
    def _shortest_path(self, source_id: str, target_id: str) -> List[str]:
        """
        Find shortest path between two nodes using BFS.
        
        Args:
            source_id: Source node ID
            target_id: Target node ID
            
        Returns:
            List of node IDs representing path, or empty list if no path
        """
        if source_id == target_id:
            return [source_id]
        
        if source_id not in self.graph.nodes or target_id not in self.graph.nodes:
            return []
        
        # BFS
        queue = deque([(source_id, [source_id])])
        visited = {source_id}
        
        while queue:
            current, path = queue.popleft()
            
            for neighbor_id in self.graph.adjacency[current]:
                if neighbor_id == target_id:
                    return path + [target_id]
                
                if neighbor_id not in visited:
                    visited.add(neighbor_id)
                    queue.append((neighbor_id, path + [neighbor_id]))
        
        return []  # No path found
    
    def _distances_from_node(self, node_id: str) -> Dict[str, int]:
        """
        Calculate distances from node to all other nodes using BFS.
        
        Args:
            node_id: Source node ID
            
        Returns:
            Dictionary mapping node ID to distance
        """
        distances: Dict[str, int] = {}
        
        if node_id not in self.graph.nodes:
            return distances
        
        queue = deque([(node_id, 0)])
        visited = {node_id}
        
        while queue:
            current, distance = queue.popleft()
            distances[current] = distance
            
            for neighbor_id in self.graph.adjacency[current]:
                if neighbor_id not in visited:
                    visited.add(neighbor_id)
                    queue.append((neighbor_id, distance + 1))
        
        return distances
    
    def get_all_centralities(self) -> Dict[str, Dict[str, float]]:
        """
        Calculate all centrality metrics for all nodes.
        
        Returns:
            Dictionary mapping node ID to centrality metrics
        """
        centralities = {}
        
        for node_id in self.graph.nodes.keys():
            centralities[node_id] = {
                "degree": self.degree_centrality(node_id),
                "betweenness": self.betweenness_centrality(node_id),
                "closeness": self.closeness_centrality(node_id),
                "clustering": self.clustering_coefficient(node_id)
            }
        
        return centralities
