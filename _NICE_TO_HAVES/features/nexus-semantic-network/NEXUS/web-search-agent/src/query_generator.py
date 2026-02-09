"""
Nexus Web Search Agent - Query Generator
Generate search queries from semantic cells
"""

from typing import List, Optional
from dataclasses import dataclass
import sys
from pathlib import Path

# Import semantic cell types
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "semantic-cells" / "src"))
from core.types import SemanticCell, CellLevel


@dataclass
class Query:
    """Search query"""
    text: str
    priority: float  # 0.0 to 1.0
    source_cell_id: Optional[str] = None


class QueryGenerator:
    """
    Query generator for generating search queries from semantic cells.
    
    Generates queries based on:
    - High uncertainty cells (high energy, high velocity)
    - Cells with few couplings
    - User-specified queries
    """
    
    def __init__(self, min_energy: float = 0.5, min_velocity: float = 0.3):
        """
        Initialize query generator.
        
        Args:
            min_energy: Minimum cell energy to generate query
            min_velocity: Minimum cell velocity to generate query
        """
        self.min_energy = min_energy
        self.min_velocity = min_velocity
    
    def generate_from_cell(self, cell: SemanticCell) -> Optional[Query]:
        """
        Generate query from semantic cell.
        
        Args:
            cell: Semantic cell
            
        Returns:
            Query or None if cell doesn't meet criteria
        """
        # Check if cell has high uncertainty (high energy/velocity)
        if cell.state.energy < self.min_energy:
            return None
        
        if abs(cell.state.velocity) < self.min_velocity:
            return None
        
        # Generate query from cell name/description
        query_text = self._cell_to_query(cell)
        
        # Calculate priority based on energy and coupling count
        priority = self._calculate_priority(cell)
        
        return Query(
            text=query_text,
            priority=priority,
            source_cell_id=cell.id
        )
    
    def generate_from_cells(self, cells: List[SemanticCell], limit: int = 10) -> List[Query]:
        """
        Generate queries from multiple semantic cells.
        
        Args:
            cells: List of semantic cells
            limit: Maximum number of queries to generate
            
        Returns:
            List of queries, sorted by priority
        """
        queries = []
        
        for cell in cells:
            query = self.generate_from_cell(cell)
            if query:
                queries.append(query)
        
        # Sort by priority (highest first)
        queries.sort(key=lambda q: q.priority, reverse=True)
        
        return queries[:limit]
    
    def generate_followup_query(self, original_query: str, search_results: List[str]) -> List[Query]:
        """
        Generate follow-up queries from search results.
        
        Args:
            original_query: Original search query
            search_results: List of search result titles/snippets
            
        Returns:
            List of follow-up queries
        """
        # Simple implementation: extract keywords from results
        # In production, would use NLP to extract entities/concepts
        
        followup_queries = []
        
        # Extract unique keywords from results
        keywords = set()
        for result in search_results[:5]:  # Use top 5 results
            words = result.lower().split()
            keywords.update([w for w in words if len(w) > 3])  # Filter short words
        
        # Generate queries combining original query with keywords
        for keyword in list(keywords)[:5]:  # Limit to 5 follow-ups
            followup_text = f"{original_query} {keyword}"
            followup_queries.append(Query(
                text=followup_text,
                priority=0.5,  # Lower priority than original
                source_cell_id=None
            ))
        
        return followup_queries
    
    def _cell_to_query(self, cell: SemanticCell) -> str:
        """
        Convert semantic cell to search query.
        
        Args:
            cell: Semantic cell
            
        Returns:
            Query string
        """
        # Use cell name as primary query
        query = cell.name
        
        # Add domain if available
        if cell.domain:
            query = f"{query} {cell.domain}"
        
        # Add description keywords if name is short
        if len(query.split()) < 3 and cell.description:
            # Extract first few words from description
            desc_words = cell.description.split()[:5]
            query = f"{query} {' '.join(desc_words)}"
        
        return query.strip()
    
    def _calculate_priority(self, cell: SemanticCell) -> float:
        """
        Calculate query priority based on cell properties.
        
        Args:
            cell: Semantic cell
            
        Returns:
            Priority (0.0 to 1.0)
        """
        # Higher energy = higher priority
        energy_factor = min(cell.state.energy, 1.0)
        
        # Higher velocity = higher priority
        velocity_factor = min(abs(cell.state.velocity), 1.0)
        
        # Fewer couplings = higher priority (less explored)
        coupling_factor = 1.0 - min(len(cell.coupling_ids) / 10.0, 1.0)
        
        # Weighted combination
        priority = (
            0.4 * energy_factor +
            0.3 * velocity_factor +
            0.3 * coupling_factor
        )
        
        return min(priority, 1.0)
