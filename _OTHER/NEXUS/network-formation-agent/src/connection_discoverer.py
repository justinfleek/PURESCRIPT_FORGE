"""
Nexus Network Formation Agent - Connection Discoverer
Discover connections between entities/concepts
"""

from typing import List, Dict, Set
from dataclasses import dataclass
import sys
from pathlib import Path

# Import types
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "content-extraction-agent" / "src"))
from entity_extractor import Entity
from relation_extractor import Relation


@dataclass
class Connection:
    """Discovered connection"""
    source_id: str
    target_id: str
    connection_type: str  # similar, related, co_occurs, etc.
    strength: float  # 0.0 to 1.0
    evidence: List[str]  # List of evidence sources
    properties: Dict = None


class ConnectionDiscoverer:
    """
    Connection discoverer for discovering connections between entities/concepts.
    
    Discovers:
    - Similar entities (based on properties, descriptions)
    - Related entities (based on relations)
    - Co-occurring entities (mentioned together)
    - Concept-entity connections
    """
    
    def __init__(self):
        """Initialize connection discoverer"""
        pass
    
    def discover_connections(
        self,
        entities: List[Entity],
        relations: List[Relation]
    ) -> List[Connection]:
        """
        Discover connections between entities.
        
        Args:
            entities: List of entities
            relations: List of relations
            
        Returns:
            List of discovered connections
        """
        connections = []
        
        # Discover connections from explicit relations
        relation_connections = self._discover_from_relations(relations)
        connections.extend(relation_connections)
        
        # Discover similar entities
        similar_connections = self._discover_similar_entities(entities)
        connections.extend(similar_connections)
        
        # Discover co-occurring entities
        co_occurrence_connections = self._discover_co_occurrence(entities, relations)
        connections.extend(co_occurrence_connections)
        
        return connections
    
    def _discover_from_relations(self, relations: List[Relation]) -> List[Connection]:
        """
        Discover connections from explicit relations.
        
        Args:
            relations: List of relations
            
        Returns:
            List of connections
        """
        connections = []
        
        for relation in relations:
            # Convert relation to connection
            connection = Connection(
                source_id=relation.source_entity_id,
                target_id=relation.target_entity_id,
                connection_type=relation.relation_type,
                strength=relation.confidence,
                evidence=[relation.evidence],
                properties={"relation_id": relation.id}
            )
            connections.append(connection)
        
        return connections
    
    def _discover_similar_entities(self, entities: List[Entity]) -> List[Connection]:
        """
        Discover similar entities based on properties.
        
        Args:
            entities: List of entities
            
        Returns:
            List of connections
        """
        connections = []
        
        # Compare entities pairwise
        for i, entity1 in enumerate(entities):
            for entity2 in entities[i+1:]:
                # Check if entities are similar
                similarity = self._calculate_similarity(entity1, entity2)
                
                if similarity > 0.5:  # Threshold
                    connections.append(Connection(
                        source_id=entity1.id,
                        target_id=entity2.id,
                        connection_type="similar",
                        strength=similarity,
                        evidence=[f"Entity similarity: {entity1.text} ~ {entity2.text}"],
                        properties={
                            "entity1_type": entity1.entity_type,
                            "entity2_type": entity2.entity_type
                        }
                    ))
        
        return connections
    
    def _discover_co_occurrence(
        self,
        entities: List[Entity],
        relations: List[Relation]
    ) -> List[Connection]:
        """
        Discover co-occurring entities.
        
        Args:
            entities: List of entities
            relations: List of relations
            
        Returns:
            List of connections
        """
        connections = []
        
        # Build entity co-occurrence graph from relations
        co_occurrence_count: Dict[tuple, int] = {}
        
        for relation in relations:
            key = tuple(sorted([relation.source_entity_id, relation.target_entity_id]))
            co_occurrence_count[key] = co_occurrence_count.get(key, 0) + 1
        
        # Create connections for frequently co-occurring entities
        for (source_id, target_id), count in co_occurrence_count.items():
            if count >= 2:  # At least 2 co-occurrences
                strength = min(count / 5.0, 1.0)  # Normalize to [0, 1]
                
                connections.append(Connection(
                    source_id=source_id,
                    target_id=target_id,
                    connection_type="co_occurs",
                    strength=strength,
                    evidence=[f"Co-occurred {count} times"],
                    properties={"co_occurrence_count": count}
                ))
        
        return connections
    
    def _calculate_similarity(self, entity1: Entity, entity2: Entity) -> float:
        """
        Calculate similarity between two entities.
        
        Args:
            entity1: First entity
            entity2: Second entity
            
        Returns:
            Similarity score (0.0 to 1.0)
        """
        # Simple similarity based on entity type and text
        similarity = 0.0
        
        # Same type bonus
        if entity1.entity_type == entity2.entity_type:
            similarity += 0.3
        
        # Text similarity (simple word overlap)
        text1_words = set(entity1.text.lower().split())
        text2_words = set(entity2.text.lower().split())
        
        if text1_words and text2_words:
            overlap = len(text1_words & text2_words) / len(text1_words | text2_words)
            similarity += 0.7 * overlap
        
        return min(similarity, 1.0)
