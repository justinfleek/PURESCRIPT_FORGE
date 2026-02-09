"""
Nexus Content Extraction Agent - Entity Extractor
Extract entities (people, places, concepts) from web content
"""

from typing import List, Dict, Any
from dataclasses import dataclass


@dataclass
class Entity:
    """Extracted entity"""
    id: str
    entity_type: str  # person, place, organization, concept, etc.
    text: str
    confidence: float  # 0.0 to 1.0
    start_pos: int  # Character position in content
    end_pos: int
    properties: Dict[str, Any] = None


class EntityExtractor:
    """
    Entity extractor for extracting entities from web content.
    
    Extracts:
    - People (names)
    - Places (locations)
    - Organizations (companies, institutions)
    - Concepts (abstract ideas)
    - Dates/Times
    - Other entities
    """
    
    def __init__(self):
        """Initialize entity extractor"""
        # Would use NLP libraries (spaCy, NLTK, etc.) in production
        pass
    
    def extract_entities(self, content: str, content_type: str = "html") -> List[Entity]:
        """
        Extract entities from content.
        
        Args:
            content: Content string
            content_type: Content type (html, text, pdf, etc.)
            
        Returns:
            List of extracted entities
        """
        # Simplified implementation - would use NLP in production
        
        entities = []
        
        # Extract text from HTML if needed
        text = self._extract_text(content, content_type)
        
        # Extract people (names) - simplified pattern matching
        people = self._extract_people(text)
        entities.extend(people)
        
        # Extract places (locations) - simplified pattern matching
        places = self._extract_places(text)
        entities.extend(places)
        
        # Extract organizations - simplified pattern matching
        organizations = self._extract_organizations(text)
        entities.extend(organizations)
        
        # Extract dates/times
        dates = self._extract_dates(text)
        entities.extend(dates)
        
        return entities
    
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
            # Simple HTML tag removal (would use BeautifulSoup in production)
            import re
            text = re.sub(r'<[^>]+>', '', content)
            text = re.sub(r'\s+', ' ', text)
            return text.strip()
        else:
            return content
    
    def _extract_people(self, text: str) -> List[Entity]:
        """
        Extract people (names) from text.
        
        Args:
            text: Text content
            
        Returns:
            List of person entities
        """
        # Simplified: look for capitalized word pairs (would use NER in production)
        import re
        
        entities = []
        
        # Pattern: Capitalized word followed by capitalized word (likely name)
        pattern = r'\b([A-Z][a-z]+)\s+([A-Z][a-z]+)\b'
        matches = re.finditer(pattern, text)
        
        for i, match in enumerate(matches):
            full_name = match.group(0)
            start_pos = match.start()
            end_pos = match.end()
            
            entities.append(Entity(
                id=f"person_{i}_{start_pos}",
                entity_type="person",
                text=full_name,
                confidence=0.6,  # Lower confidence for pattern-based extraction
                start_pos=start_pos,
                end_pos=end_pos,
                properties={"first_name": match.group(1), "last_name": match.group(2)}
            ))
        
        return entities
    
    def _extract_places(self, text: str) -> List[Entity]:
        """
        Extract places (locations) from text.
        
        Args:
            text: Text content
            
        Returns:
            List of place entities
        """
        # Simplified: look for common place indicators (would use NER in production)
        import re
        
        entities = []
        
        # Common place patterns
        place_patterns = [
            r'\b([A-Z][a-z]+(?:\s+[A-Z][a-z]+)*)\s+(?:City|State|Country|Province|Region)\b',
            r'\b(?:in|at|from|to)\s+([A-Z][a-z]+(?:\s+[A-Z][a-z]+)*)\b',
        ]
        
        for pattern in place_patterns:
            matches = re.finditer(pattern, text, re.IGNORECASE)
            for i, match in enumerate(matches):
                place_name = match.group(1) if match.groups() else match.group(0)
                start_pos = match.start()
                end_pos = match.end()
                
                entities.append(Entity(
                    id=f"place_{i}_{start_pos}",
                    entity_type="place",
                    text=place_name,
                    confidence=0.5,
                    start_pos=start_pos,
                    end_pos=end_pos
                ))
        
        return entities
    
    def _extract_organizations(self, text: str) -> List[Entity]:
        """
        Extract organizations from text.
        
        Args:
            text: Text content
            
        Returns:
            List of organization entities
        """
        # Simplified: look for organization indicators (would use NER in production)
        import re
        
        entities = []
        
        # Common organization patterns
        org_patterns = [
            r'\b([A-Z][a-zA-Z]+(?:\s+[A-Z][a-zA-Z]+)*)\s+(?:Inc|LLC|Corp|Ltd|Company|Corporation)\b',
            r'\b([A-Z][a-zA-Z]+(?:\s+[A-Z][a-zA-Z]+)*)\s+(?:University|College|Institute|Laboratory|Lab)\b',
        ]
        
        for pattern in org_patterns:
            matches = re.finditer(pattern, text)
            for i, match in enumerate(matches):
                org_name = match.group(1)
                start_pos = match.start()
                end_pos = match.end()
                
                entities.append(Entity(
                    id=f"org_{i}_{start_pos}",
                    entity_type="organization",
                    text=org_name,
                    confidence=0.6,
                    start_pos=start_pos,
                    end_pos=end_pos
                ))
        
        return entities
    
    def _extract_dates(self, text: str) -> List[Entity]:
        """
        Extract dates/times from text.
        
        Args:
            text: Text content
            
        Returns:
            List of date entities
        """
        # Simplified: look for date patterns (would use date parser in production)
        import re
        
        entities = []
        
        # Common date patterns
        date_patterns = [
            r'\b(\d{1,2}[/-]\d{1,2}[/-]\d{2,4})\b',  # MM/DD/YYYY
            r'\b([A-Z][a-z]+\s+\d{1,2},?\s+\d{4})\b',  # Month DD, YYYY
            r'\b(\d{4})\b',  # Year
        ]
        
        for pattern in date_patterns:
            matches = re.finditer(pattern, text)
            for i, match in enumerate(matches):
                date_text = match.group(0)
                start_pos = match.start()
                end_pos = match.end()
                
                entities.append(Entity(
                    id=f"date_{i}_{start_pos}",
                    entity_type="date",
                    text=date_text,
                    confidence=0.7,
                    start_pos=start_pos,
                    end_pos=end_pos
                ))
        
        return entities
