"""
Nexus Content Extraction Agent - Relation Extractor
Extract relationships between entities
"""

from typing import List, Dict, Any
from dataclasses import dataclass
from .entity_extractor import Entity


@dataclass
class Relation:
    """Extracted relation"""
    id: str
    source_entity_id: str
    target_entity_id: str
    relation_type: str  # works_at, located_in, founded_by, etc.
    confidence: float  # 0.0 to 1.0
    evidence: str  # Text evidence for relation
    properties: Dict[str, Any] = None


class RelationExtractor:
    """
    Relation extractor for extracting relationships between entities.
    
    Extracts:
    - Works at (person -> organization)
    - Located in (entity -> place)
    - Founded by (organization -> person)
    - Related to (entity -> entity)
    - Other relations
    """
    
    def __init__(self):
        """Initialize relation extractor"""
        # Would use relation extraction models in production
        pass
    
    def extract_relations(
        self,
        entities: List[Entity],
        content: str
    ) -> List[Relation]:
        """
        Extract relations between entities.
        
        Args:
            entities: List of extracted entities
            content: Original content text
            
        Returns:
            List of extracted relations
        """
        relations = []
        
        # Extract works_at relations (person -> organization)
        works_at = self._extract_works_at(entities, content)
        relations.extend(works_at)
        
        # Extract located_in relations (entity -> place)
        located_in = self._extract_located_in(entities, content)
        relations.extend(located_in)
        
        # Extract founded_by relations (organization -> person)
        founded_by = self._extract_founded_by(entities, content)
        relations.extend(founded_by)
        
        # Extract co-occurrence relations (entities mentioned together)
        co_occurrence = self._extract_co_occurrence(entities, content)
        relations.extend(co_occurrence)
        
        return relations
    
    def _extract_works_at(
        self,
        entities: List[Entity],
        content: str
    ) -> List[Relation]:
        """
        Extract "works at" relations (person -> organization).
        
        Args:
            entities: List of entities
            content: Content text
            
        Returns:
            List of relations
        """
        relations = []
        
        people = [e for e in entities if e.entity_type == "person"]
        organizations = [e for e in entities if e.entity_type == "organization"]
        
        # Look for patterns like "John works at Company"
        import re
        
        for person in people:
            for org in organizations:
                # Check if person and org are mentioned near each other
                person_pos = person.start_pos
                org_pos = org.start_pos
                
                # Extract context between entities
                start = min(person_pos, org_pos)
                end = max(person_pos + len(person.text), org_pos + len(org.text))
                context = content[start:end]
                
                # Look for relation indicators
                relation_patterns = [
                    r'\b(?:works?\s+at|employed\s+by|employee\s+of)\b',
                    r'\b(?:CEO|CTO|CFO|President|Director)\s+of\b',
                ]
                
                for pattern in relation_patterns:
                    if re.search(pattern, context, re.IGNORECASE):
                        relations.append(Relation(
                            id=f"works_at_{person.id}_{org.id}",
                            source_entity_id=person.id,
                            target_entity_id=org.id,
                            relation_type="works_at",
                            confidence=0.7,
                            evidence=context
                        ))
                        break
        
        return relations
    
    def _extract_located_in(
        self,
        entities: List[Entity],
        content: str
    ) -> List[Relation]:
        """
        Extract "located in" relations (entity -> place).
        
        Args:
            entities: List of entities
            content: Content text
            
        Returns:
            List of relations
        """
        relations = []
        
        places = [e for e in entities if e.entity_type == "place"]
        other_entities = [e for e in entities if e.entity_type != "place"]
        
        import re
        
        for entity in other_entities:
            for place in places:
                # Check proximity
                entity_pos = entity.start_pos
                place_pos = place.start_pos
                
                start = min(entity_pos, place_pos)
                end = max(entity_pos + len(entity.text), place_pos + len(place.text))
                context = content[start:end]
                
                # Look for location indicators
                location_patterns = [
                    r'\b(?:located\s+in|based\s+in|in|at)\b',
                    r'\b(?:from|near|around)\b',
                ]
                
                for pattern in location_patterns:
                    if re.search(pattern, context, re.IGNORECASE):
                        relations.append(Relation(
                            id=f"located_in_{entity.id}_{place.id}",
                            source_entity_id=entity.id,
                            target_entity_id=place.id,
                            relation_type="located_in",
                            confidence=0.6,
                            evidence=context
                        ))
                        break
        
        return relations
    
    def _extract_founded_by(
        self,
        entities: List[Entity],
        content: str
    ) -> List[Relation]:
        """
        Extract "founded by" relations (organization -> person).
        
        Args:
            entities: List of entities
            content: Content text
            
        Returns:
            List of relations
        """
        relations = []
        
        organizations = [e for e in entities if e.entity_type == "organization"]
        people = [e for e in entities if e.entity_type == "person"]
        
        import re
        
        for org in organizations:
            for person in people:
                org_pos = org.start_pos
                person_pos = person.start_pos
                
                start = min(org_pos, person_pos)
                end = max(org_pos + len(org.text), person_pos + len(person.text))
                context = content[start:end]
                
                # Look for founder patterns
                founder_patterns = [
                    r'\b(?:founded\s+by|created\s+by|established\s+by)\b',
                    r'\b(?:founder|co-founder|creator)\b',
                ]
                
                for pattern in founder_patterns:
                    if re.search(pattern, context, re.IGNORECASE):
                        relations.append(Relation(
                            id=f"founded_by_{org.id}_{person.id}",
                            source_entity_id=org.id,
                            target_entity_id=person.id,
                            relation_type="founded_by",
                            confidence=0.7,
                            evidence=context
                        ))
                        break
        
        return relations
    
    def _extract_co_occurrence(
        self,
        entities: List[Entity],
        content: str
    ) -> List[Relation]:
        """
        Extract co-occurrence relations (entities mentioned together).
        
        Args:
            entities: List of entities
            content: Content text
            
        Returns:
            List of relations
        """
        relations = []
        
        # Find entities mentioned within a window of each other
        window_size = 200  # characters
        
        for i, entity1 in enumerate(entities):
            for entity2 in entities[i+1:]:
                # Check if entities are close together
                pos1 = entity1.start_pos
                pos2 = entity2.start_pos
                
                distance = abs(pos1 - pos2)
                
                if distance < window_size:
                    # Extract context
                    start = min(pos1, pos2)
                    end = max(pos1 + len(entity1.text), pos2 + len(entity2.text))
                    context = content[start:end]
                    
                    relations.append(Relation(
                        id=f"co_occurrence_{entity1.id}_{entity2.id}",
                        source_entity_id=entity1.id,
                        target_entity_id=entity2.id,
                        relation_type="co_occurrence",
                        confidence=0.4,  # Lower confidence for co-occurrence
                        evidence=context
                    ))
        
        return relations
