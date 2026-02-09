"""
Nexus Content Extraction Agent - Concept Extractor
Extract abstract concepts from web content
"""

from typing import List, Dict, Any
from dataclasses import dataclass


@dataclass
class Concept:
    """Extracted concept"""
    id: str
    name: str
    description: str
    domain: str
    confidence: float  # 0.0 to 1.0
    properties: Dict[str, Any] = None


class ConceptExtractor:
    """
    Concept extractor for extracting abstract concepts from content.
    
    Extracts:
    - Abstract concepts (ideas, theories, methods)
    - Domain-specific concepts
    - Technical concepts
    """
    
    def __init__(self):
        """Initialize concept extractor"""
        # Would use concept extraction models in production
        pass
    
    def extract_concepts(self, content: str, content_type: str = "html") -> List[Concept]:
        """
        Extract concepts from content.
        
        Args:
            content: Content string
            content_type: Content type
            
        Returns:
            List of extracted concepts
        """
        # Simplified implementation - would use NLP/concept extraction in production
        
        concepts = []
        
        # Extract text
        text = self._extract_text(content, content_type)
        
        # Extract technical concepts (simplified keyword-based)
        technical = self._extract_technical_concepts(text)
        concepts.extend(technical)
        
        # Extract domain concepts (simplified)
        domain_concepts = self._extract_domain_concepts(text)
        concepts.extend(domain_concepts)
        
        return concepts
    
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
    
    def _extract_technical_concepts(self, text: str) -> List[Concept]:
        """
        Extract technical concepts from text.
        
        Args:
            text: Text content
            
        Returns:
            List of technical concepts
        """
        # Simplified: look for technical terms (would use domain knowledge in production)
        import re
        
        concepts = []
        
        # Common technical concept patterns
        technical_terms = [
            r'\b(machine\s+learning|deep\s+learning|neural\s+network)\b',
            r'\b(artificial\s+intelligence|AI|ML)\b',
            r'\b(blockchain|cryptocurrency|bitcoin)\b',
            r'\b(quantum\s+computing|quantum\s+mechanics)\b',
            r'\b(cloud\s+computing|distributed\s+systems)\b',
        ]
        
        for pattern in technical_terms:
            matches = re.finditer(pattern, text, re.IGNORECASE)
            for i, match in enumerate(matches):
                concept_name = match.group(0)
                start_pos = match.start()
                
                # Extract surrounding context as description
                context_start = max(0, start_pos - 50)
                context_end = min(len(text), start_pos + len(concept_name) + 50)
                description = text[context_start:context_end].strip()
                
                concepts.append(Concept(
                    id=f"technical_{i}_{start_pos}",
                    name=concept_name,
                    description=description,
                    domain="technology",
                    confidence=0.6,
                    properties={"type": "technical"}
                ))
        
        return concepts
    
    def _extract_domain_concepts(self, text: str) -> List[Concept]:
        """
        Extract domain-specific concepts from text.
        
        Args:
            text: Text content
            
        Returns:
            List of domain concepts
        """
        # Simplified: look for domain-specific terms
        import re
        
        concepts = []
        
        # Domain concept patterns (simplified)
        domain_patterns = [
            (r'\b([A-Z][a-z]+(?:\s+[A-Z][a-z]+)*)\s+(?:theory|method|approach|framework)\b', "theory"),
            (r'\b([A-Z][a-z]+(?:\s+[A-Z][a-z]+)*)\s+(?:algorithm|technique|process)\b', "method"),
        ]
        
        for pattern, concept_type in domain_patterns:
            matches = re.finditer(pattern, text)
            for i, match in enumerate(matches):
                concept_name = match.group(1) if match.groups() else match.group(0)
                start_pos = match.start()
                
                # Extract context
                context_start = max(0, start_pos - 50)
                context_end = min(len(text), start_pos + len(concept_name) + 50)
                description = text[context_start:context_end].strip()
                
                concepts.append(Concept(
                    id=f"domain_{concept_type}_{i}_{start_pos}",
                    name=concept_name,
                    description=description,
                    domain="general",
                    confidence=0.5,
                    properties={"type": concept_type}
                ))
        
        return concepts
