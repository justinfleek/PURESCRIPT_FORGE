"""
Nexus Network Graph - Persistence
Save/load network graphs
"""

import json
from pathlib import Path
from typing import Optional
from .graph import NetworkGraph


class GraphPersistence:
    """
    Graph persistence for saving and loading network graphs.
    
    Supports JSON serialization for graph storage.
    """
    
    @staticmethod
    def save_graph(graph: NetworkGraph, path: str) -> None:
        """
        Save graph to file.
        
        Args:
            graph: Network graph
            path: File path
        """
        file_path = Path(path)
        file_path.parent.mkdir(parents=True, exist_ok=True)
        
        graph_dict = graph.to_dict()
        
        with open(file_path, 'w') as f:
            json.dump(graph_dict, f, indent=2)
    
    @staticmethod
    def load_graph(path: str) -> Optional[NetworkGraph]:
        """
        Load graph from file.
        
        Args:
            path: File path
            
        Returns:
            Network graph or None if file not found
        """
        file_path = Path(path)
        
        if not file_path.exists():
            return None
        
        with open(file_path, 'r') as f:
            graph_dict = json.load(f)
        
        return NetworkGraph.from_dict(graph_dict)
