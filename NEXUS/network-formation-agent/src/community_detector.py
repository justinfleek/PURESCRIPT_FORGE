"""
Nexus Network Formation Agent - Community Detector
Detect communities in network graph
"""

from typing import List
import sys
from pathlib import Path

# Import network graph types
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "network-graph" / "src"))
from graph import NetworkGraph, Community


class CommunityDetector:
    """
    Community detector for detecting communities in network graph.
    
    Uses simple connected components algorithm.
    More sophisticated algorithms (Louvain, Leiden) would be used in production.
    """
    
    def __init__(self, graph: NetworkGraph):
        """
        Initialize community detector.
        
        Args:
            graph: Network graph
        """
        self.graph = graph
    
    def detect_communities(self) -> List[Community]:
        """
        Detect communities in network graph.
        
        Returns:
            List of communities
        """
        from collections import deque
        
        visited: set = set()
        communities: List[Community] = []
        community_id = 0
        
        for node_id in self.graph.nodes.keys():
            if node_id in visited:
                continue
            
            # BFS to find connected component
            community_nodes = []
            queue = deque([node_id])
            visited.add(node_id)
            
            while queue:
                current = queue.popleft()
                community_nodes.append(current)
                
                # Get neighbors
                neighbors = self.graph.get_neighbors(current)
                for neighbor in neighbors:
                    if neighbor.id not in visited:
                        visited.add(neighbor.id)
                        queue.append(neighbor.id)
            
            if community_nodes:
                community = Community(
                    id=f"community_{community_id}",
                    node_ids=community_nodes,
                    properties={
                        "size": len(community_nodes),
                        "density": self._calculate_density(community_nodes)
                    }
                )
                communities.append(community)
                community_id += 1
        
        return communities
    
    def _calculate_density(self, node_ids: List[str]) -> float:
        """
        Calculate community density (fraction of possible edges present).
        
        Args:
            node_ids: List of node IDs in community
            
        Returns:
            Density (0.0 to 1.0)
        """
        if len(node_ids) < 2:
            return 0.0
        
        # Count edges within community
        edge_count = 0
        for source_id in node_ids:
            neighbors = self.graph.get_neighbors(source_id)
            for neighbor in neighbors:
                if neighbor.id in node_ids:
                    edge_count += 1
        
        # Divide by 2 (undirected graph)
        edge_count = edge_count // 2
        
        # Possible edges = n * (n-1) / 2
        possible_edges = len(node_ids) * (len(node_ids) - 1) / 2
        
        if possible_edges == 0:
            return 0.0
        
        return edge_count / possible_edges
