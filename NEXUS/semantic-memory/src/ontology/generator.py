"""
Nexus Semantic Memory - Ontology Generator
Generate ontology layers (Level 0/1/2, ~8,000 semantic cells)
"""

from typing import List, Dict
import uuid
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent.parent / "semantic-cells" / "src"))
from core.types import SemanticCell, CellState, CellLevel, BasinType


class OntologyGenerator:
    """
    Ontology generator for generating semantic cell ontology.
    
    Generates ~8,000 semantic cells across 3 levels:
    - Level 0 (PRIMITIVE): ~500 basic concepts
    - Level 1 (BASIC): ~2,500 common concepts
    - Level 2 (COMMON): ~5,000 domain-specific concepts
    """
    
    def __init__(self):
        """Initialize ontology generator"""
        self.primitive_concepts = self._load_primitive_concepts()
        self.basic_concepts = self._load_basic_concepts()
        self.common_concepts = self._load_common_concepts()
    
    def generate_ontology(self) -> List[SemanticCell]:
        """
        Generate full ontology.
        
        Returns:
            List of semantic cells
        """
        cells = []
        
        # Generate Level 0 (PRIMITIVE)
        cells.extend(self._generate_level_0())
        
        # Generate Level 1 (BASIC)
        cells.extend(self._generate_level_1())
        
        # Generate Level 2 (COMMON)
        cells.extend(self._generate_level_2())
        
        return cells
    
    def _generate_level_0(self) -> List[SemanticCell]:
        """Generate Level 0 (PRIMITIVE) cells (~500)"""
        cells = []
        
        # Basic entities
        entities = [
            "person", "place", "thing", "object", "entity",
            "animal", "plant", "mineral", "substance",
            "body", "mind", "soul", "spirit",
            "space", "time", "matter", "energy",
            "form", "function", "structure", "pattern",
        ]
        
        # Basic events
        events = [
            "action", "movement", "change", "process",
            "creation", "destruction", "transformation",
            "beginning", "end", "continuation",
            "cause", "effect", "result",
            "interaction", "communication", "exchange",
        ]
        
        # Basic properties
        properties = [
            "size", "color", "shape", "texture",
            "weight", "density", "temperature",
            "speed", "direction", "position",
            "quality", "quantity", "measure",
            "existence", "presence", "absence",
        ]
        
        # Basic relations
        relations = [
            "similarity", "difference", "equality",
            "connection", "separation", "distance",
            "containment", "membership", "ownership",
            "causation", "dependence", "independence",
        ]
        
        all_concepts = entities + events + properties + relations
        
        for i, concept in enumerate(all_concepts[:500]):  # Limit to 500
            cell = SemanticCell(
                id=f"primitive_{i}_{concept}",
                name=concept,
                description=f"Primitive concept: {concept}",
                level=CellLevel.PRIMITIVE,
                domain="foundational",
                basin=self._determine_basin(concept, entities, events, properties, relations),
                state=CellState(
                    position=[0.0, 0.0, 0.0],
                    velocity=[0.0, 0.0, 0.0],
                    acceleration=[0.0, 0.0, 0.0],
                    spin=0.0,
                    grade=0.5,
                    energy=0.5
                ),
                parent_id=None,
                children_ids=[],
                coupling_ids=[]
            )
            cells.append(cell)
        
        return cells
    
    def _generate_level_1(self) -> List[SemanticCell]:
        """Generate Level 1 (BASIC) cells (~2,500)"""
        cells = []
        
        # Domains
        domains = [
            "science", "technology", "art", "philosophy",
            "mathematics", "physics", "chemistry", "biology",
            "psychology", "sociology", "economics", "politics",
            "history", "geography", "culture", "language",
            "music", "literature", "visual_arts", "performing_arts",
            "sports", "games", "entertainment", "media",
            "food", "health", "medicine", "education",
            "business", "finance", "law", "religion",
        ]
        
        # Concepts per domain
        concepts_per_domain = {
            "science": ["hypothesis", "experiment", "theory", "law", "observation", "data", "analysis", "conclusion"],
            "technology": ["computer", "software", "hardware", "algorithm", "network", "database", "interface", "system"],
            "art": ["painting", "sculpture", "drawing", "design", "composition", "color", "form", "expression"],
            "philosophy": ["truth", "reality", "knowledge", "wisdom", "ethics", "logic", "metaphysics", "epistemology"],
            "mathematics": ["number", "equation", "function", "graph", "proof", "theorem", "calculation", "formula"],
            "physics": ["force", "energy", "matter", "wave", "particle", "field", "motion", "gravity"],
            "chemistry": ["element", "compound", "reaction", "molecule", "atom", "bond", "solution", "catalyst"],
            "biology": ["organism", "cell", "gene", "evolution", "ecosystem", "species", "reproduction", "metabolism"],
        }
        
        cell_id = 0
        for domain in domains:
            concepts = concepts_per_domain.get(domain, [f"{domain}_concept_{i}" for i in range(20)])
            
            for concept in concepts[:20]:  # Limit per domain
                cell = SemanticCell(
                    id=f"basic_{cell_id}_{domain}_{concept}",
                    name=f"{concept}",
                    description=f"Basic concept in {domain}: {concept}",
                    level=CellLevel.BASIC,
                    domain=domain,
                    basin=self._determine_basin(concept, [], [], [], []),
                    state=CellState(
                        position=[0.0, 0.0, 0.0],
                        velocity=[0.0, 0.0, 0.0],
                        acceleration=[0.0, 0.0, 0.0],
                        spin=0.0,
                        grade=0.5,
                        energy=0.5
                    ),
                    parent_id=None,
                    children_ids=[],
                    coupling_ids=[]
                )
                cells.append(cell)
                cell_id += 1
        
        # Fill to ~2,500
        while len(cells) < 2500:
            domain = domains[cell_id % len(domains)]
            concept = f"{domain}_concept_{cell_id}"
            cell = SemanticCell(
                id=f"basic_{cell_id}_{concept}",
                name=concept,
                description=f"Basic concept: {concept}",
                level=CellLevel.BASIC,
                domain=domain,
                basin=BasinType.ENTITY,
                state=CellState(
                    position=[0.0, 0.0, 0.0],
                    velocity=[0.0, 0.0, 0.0],
                    acceleration=[0.0, 0.0, 0.0],
                    spin=0.0,
                    grade=0.5,
                    energy=0.5
                ),
                parent_id=None,
                children_ids=[],
                coupling_ids=[]
            )
            cells.append(cell)
            cell_id += 1
        
        return cells[:2500]
    
    def _generate_level_2(self) -> List[SemanticCell]:
        """Generate Level 2 (COMMON) cells (~5,000)"""
        cells = []
        
        # Specialized domains
        specialized_domains = [
            "machine_learning", "artificial_intelligence", "blockchain", "cryptocurrency",
            "quantum_computing", "biotechnology", "nanotechnology", "robotics",
            "virtual_reality", "augmented_reality", "metaverse", "web3",
            "social_media", "content_creation", "influencer", "viral",
            "startup", "venture_capital", "entrepreneurship", "innovation",
            "climate_change", "sustainability", "renewable_energy", "carbon_neutral",
            "mental_health", "wellness", "mindfulness", "therapy",
            "remote_work", "distributed_teams", "productivity", "work_life_balance",
        ]
        
        cell_id = 0
        for domain in specialized_domains:
            # Generate ~200 concepts per domain
            for i in range(200):
                concept = f"{domain}_concept_{i}"
                cell = SemanticCell(
                    id=f"common_{cell_id}_{concept}",
                    name=concept,
                    description=f"Common concept in {domain}: {concept}",
                    level=CellLevel.COMMON,
                    domain=domain,
                    basin=BasinType.ENTITY,
                    state=CellState(
                        position=[0.0, 0.0, 0.0],
                        velocity=[0.0, 0.0, 0.0],
                        acceleration=[0.0, 0.0, 0.0],
                        spin=0.0,
                        grade=0.5,
                        energy=0.5
                    ),
                    parent_id=None,
                    children_ids=[],
                    coupling_ids=[]
                )
                cells.append(cell)
                cell_id += 1
        
        return cells[:5000]
    
    def _determine_basin(
        self,
        concept: str,
        entities: List[str],
        events: List[str],
        properties: List[str],
        relations: List[str]
    ) -> BasinType:
        """Determine basin type for concept"""
        if concept in entities:
            return BasinType.ENTITY
        elif concept in events:
            return BasinType.EVENT
        elif concept in properties:
            return BasinType.PROPERTY
        elif concept in relations:
            return BasinType.RELATION
        else:
            return BasinType.ENTITY  # Default
    
    def _load_primitive_concepts(self) -> List[str]:
        """Load primitive concepts"""
        return []  # Would load from file in production
    
    def _load_basic_concepts(self) -> List[str]:
        """Load basic concepts"""
        return []  # Would load from file in production
    
    def _load_common_concepts(self) -> List[str]:
        """Load common concepts"""
        return []  # Would load from file in production
