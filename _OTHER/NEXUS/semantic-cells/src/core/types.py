"""
Nexus Core Types
Semantic Cell Architecture - Core Data Structures

This module defines the core data structures for semantic cells:
- SemanticCell: A predictive agent representing a concept
- CellState: Dynamic state of a cell (position, velocity, spin, etc.)
- Coupling: Connection between cells
- BasinType: Attractor type for semantic organization
"""

from dataclasses import dataclass
from typing import List, Optional
from enum import Enum


class CellLevel(Enum):
    """Ontology level for semantic cells"""
    PRIMITIVE = "primitive"  # Level 0: ~200 fundamental concepts
    BASIC = "basic"          # Level 1: ~2,000 common categories
    COMMON = "common"        # Level 2: ~6,000 specific concepts


class BasinType(Enum):
    """Attractor type for semantic organization"""
    ENTITY = "entity"        # Things (DOG, CAT, PERSON)
    EVENT = "event"          # Actions (RUNNING, EATING, SLEEPING)
    PROPERTY = "property"    # Qualities (RED, FAST, HEAVY)
    RELATION = "relation"    # Connections (PART_OF, CONTAINS, NEAR)
    CAUSE = "cause"          # Causation (CAUSES, ENABLES, PREVENTS)


class CouplingType(Enum):
    """Type of coupling between cells"""
    IS_A = "is_a"                    # Hierarchical (DOG IS_A MAMMAL)
    HAS = "has"                      # Composition (CAR HAS WHEEL)
    CAUSES = "causes"                # Causation (RAIN CAUSES WET)
    SIMILAR = "similar"               # Similarity (DOG SIMILAR WOLF)
    PART_OF = "part_of"               # Part-whole (WHEEL PART_OF CAR)
    CONTAINS = "contains"             # Containment (BOX CONTAINS ITEM)
    NEAR = "near"                     # Spatial proximity
    TEMPORAL = "temporal"             # Temporal relation (BEFORE, AFTER)
    FUNCTIONAL = "functional"         # Functional relation (USES, CREATES)


@dataclass
class CellState:
    """
    Dynamic state of a semantic cell.
    
    Each cell maintains:
    - position: 512-dim embedding position in semantic space
    - velocity: Rate of change (first derivative)
    - acceleration: Second derivative
    - spin: 3D attention direction vector
    - grade: Confidence level (0-1)
    - energy: Activation level (0-1)
    """
    position: List[float]      # 512-dim embedding position
    velocity: List[float]      # Rate of change
    acceleration: List[float]   # Second derivative
    spin: List[float]          # 3D attention direction [x, y, z]
    grade: float               # Confidence (0-1)
    energy: float              # Activation level (0-1)
    
    def __post_init__(self):
        """Validate state dimensions"""
        assert len(self.position) == 512, "Position must be 512-dim"
        assert len(self.velocity) == 512, "Velocity must be 512-dim"
        assert len(self.acceleration) == 512, "Acceleration must be 512-dim"
        assert len(self.spin) == 3, "Spin must be 3D"
        assert 0.0 <= self.grade <= 1.0, "Grade must be in [0, 1]"
        assert 0.0 <= self.energy <= 1.0, "Energy must be in [0, 1]"


@dataclass
class SemanticCell:
    """
    A semantic cell - a predictive agent representing a concept.
    
    Each cell:
    - Has a unique identifier and human-readable name
    - Belongs to an ontology level (PRIMITIVE, BASIC, COMMON)
    - Has a domain category (ANIMAL, EMOTION, TOOL, etc.)
    - Belongs to a basin (attractor type)
    - Maintains dynamic state (position, velocity, spin, etc.)
    - Has hierarchical relationships (parent, children)
    - Connects to other cells via couplings
    """
    id: str                    # Unique identifier
    name: str                  # Human-readable name
    description: str           # What this concept means
    level: CellLevel           # PRIMITIVE, BASIC, or COMMON
    domain: str                # Category (ANIMAL, EMOTION, TOOL, etc.)
    basin: BasinType           # Attractor type (ENTITY, EVENT, etc.)
    state: CellState           # Current dynamic state
    parent_id: Optional[str]   # Hierarchical parent
    children_ids: List[str]    # Hierarchical children
    coupling_ids: List[str]    # Connected cells (via couplings)
    
    def __post_init__(self):
        """Validate cell structure"""
        assert self.id, "Cell must have an ID"
        assert self.name, "Cell must have a name"
        assert self.description, "Cell must have a description"
        if self.parent_id:
            assert self.parent_id != self.id, "Cell cannot be its own parent"


@dataclass
class Coupling:
    """
    A coupling between two semantic cells.
    
    Couplings enable information flow between cells:
    - source_id: Source cell
    - target_id: Target cell
    - coupling_type: Type of relationship
    - strength: Coupling strength (0-1)
    - bidirectional: Whether coupling works both ways
    """
    id: str
    source_id: str
    target_id: str
    coupling_type: CouplingType
    strength: float            # 0-1
    bidirectional: bool
    
    def __post_init__(self):
        """Validate coupling"""
        assert self.source_id != self.target_id, "Source and target must differ"
        assert 0.0 <= self.strength <= 1.0, "Strength must be in [0, 1]"
