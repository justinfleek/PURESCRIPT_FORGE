"""
Nexus Network Formation Agent - Weight Calculator
Calculate edge weights (strength of connection)
"""

from typing import List
from dataclasses import dataclass
import sys
from pathlib import Path

# Import types
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "network-graph" / "src"))
from graph import Edge

sys.path.insert(0, str(Path(__file__).parent.parent.parent / "network-formation-agent" / "src"))
from connection_discoverer import Connection


@dataclass
class Evidence:
    """Evidence for connection"""
    source: str  # discovery, relation, co_occurrence, etc.
    strength: float  # 0.0 to 1.0
    timestamp: str


class WeightCalculator:
    """
    Weight calculator for calculating edge weights.
    
    Calculates weights based on:
    - Discovery frequency
    - Semantic similarity
    - Temporal proximity
    - Agent consensus
    """
    
    def __init__(self):
        """Initialize weight calculator"""
        pass
    
    def calculate_weight(
        self,
        edge: Edge,
        evidence: List[Evidence]
    ) -> float:
        """
        Calculate edge weight from evidence.
        
        Args:
            edge: Network edge
            evidence: List of evidence
            
        Returns:
            Weight (0.0 to 1.0)
        """
        if not evidence:
            return edge.weight  # Use existing weight
        
        # Calculate weighted average of evidence strengths
        total_weight = 0.0
        total_strength = 0.0
        
        for ev in evidence:
            # Weight by evidence source type
            source_weight = self._get_source_weight(ev.source)
            
            total_weight += source_weight
            total_strength += ev.strength * source_weight
        
        if total_weight == 0:
            return edge.weight
        
        # Normalize to [0, 1]
        calculated_weight = total_strength / total_weight
        
        # Combine with existing weight (weighted average)
        combined_weight = 0.7 * calculated_weight + 0.3 * edge.weight
        
        return min(combined_weight, 1.0)
    
    def calculate_weight_from_connection(
        self,
        connection: Connection
    ) -> float:
        """
        Calculate weight directly from connection.
        
        Args:
            connection: Connection
            
        Returns:
            Weight (0.0 to 1.0)
        """
        base_weight = connection.strength
        
        # Adjust based on evidence count
        evidence_count = len(connection.evidence)
        evidence_bonus = min(evidence_count / 5.0, 0.2)  # Up to 0.2 bonus
        
        final_weight = min(base_weight + evidence_bonus, 1.0)
        
        return final_weight
    
    def _get_source_weight(self, source: str) -> float:
        """
        Get weight for evidence source type.
        
        Args:
            source: Evidence source type
            
        Returns:
            Source weight
        """
        # Different sources have different reliability
        source_weights = {
            "relation": 1.0,  # Explicit relations are most reliable
            "discovery": 0.8,  # Discoveries are reliable
            "co_occurrence": 0.6,  # Co-occurrence is less reliable
            "similarity": 0.5,  # Similarity is least reliable
        }
        
        return source_weights.get(source, 0.5)
