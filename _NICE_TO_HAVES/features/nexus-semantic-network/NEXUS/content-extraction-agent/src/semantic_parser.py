"""
Nexus Content Extraction Agent - Semantic Parser
Parse semantic structure from text
"""

from typing import List, Dict, Any
from dataclasses import dataclass
from .entity_extractor import Entity
from .relation_extractor import Relation
from .concept_extractor import Concept


@dataclass
class SemanticStructure:
    """Semantic structure extracted from content"""
    content_id: str
    entities: List[Entity]
    relations: List[Relation]
    concepts: List[Concept]
    summary: str
    properties: Dict[str, Any] = None


class SemanticParser:
    """
    Semantic parser for parsing semantic structure from text.
    
    Combines entity extraction, relation extraction, and concept extraction
    into a unified semantic structure.
    """
    
    def __init__(self):
        """Initialize semantic parser"""
        from .entity_extractor import EntityExtractor
        from .relation_extractor import RelationExtractor
        from .concept_extractor import ConceptExtractor
        
        self.entity_extractor = EntityExtractor()
        self.relation_extractor = RelationExtractor()
        self.concept_extractor = ConceptExtractor()
    
    def parse_semantic_structure(
        self,
        content: str,
        content_id: str,
        content_type: str = "html"
    ) -> SemanticStructure:
        """
        Parse semantic structure from content.
        
        Args:
            content: Content string
            content_id: Content ID
            content_type: Content type
            
        Returns:
            Semantic structure
        """
        # Extract text
        text = self._extract_text(content, content_type)
        
        # Extract entities
        entities = self.entity_extractor.extract_entities(content, content_type)
        
        # Extract relations between entities
        relations = self.relation_extractor.extract_relations(entities, text)
        
        # Extract concepts
        concepts = self.concept_extractor.extract_concepts(content, content_type)
        
        # Generate summary
        summary = self._generate_summary(text, entities, concepts)
        
        return SemanticStructure(
            content_id=content_id,
            entities=entities,
            relations=relations,
            concepts=concepts,
            summary=summary,
            properties={
                "entity_count": len(entities),
                "relation_count": len(relations),
                "concept_count": len(concepts)
            }
        )
    
    def _extract_text(self, content: str, content_type: str) -> str:
        """
        Extract plain text from content.
        
        Args:
            content: Content string
            content_type: Content type
            
        Returns:
            Plain text
        """
        if content_type == "html":
            import re
            text = re.sub(r'<[^>]+>', '', content)
            text = re.sub(r'\s+', ' ', text)
            return text.strip()
        else:
            return content
    
    def _generate_summary(
        self,
        text: str,
        entities: List[Entity],
        concepts: List[Concept]
    ) -> str:
        """
        Generate summary from extracted entities and concepts.
        
        Args:
            text: Original text
            entities: Extracted entities
            concepts: Extracted concepts
            
        Returns:
            Summary string
        """
        # Simplified: extract first few sentences (would use summarization model in production)
        sentences = text.split('.')
        
        # Take first 3 sentences as summary
        summary_sentences = sentences[:3]
        summary = '. '.join(summary_sentences).strip()
        
        if summary and not summary.endswith('.'):
            summary += '.'
        
        return summary
