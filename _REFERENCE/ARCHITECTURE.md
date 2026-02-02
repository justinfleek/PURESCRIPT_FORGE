# Semantic Cell Architecture
## A Predictive Processing Framework for Living Meaning

---

## Executive Summary

We are building a **semantic memory system** where concepts are not static embeddings but **living predictive agents**. Each semantic cell:

1. **Predicts** its own future state using a small neural network
2. **Allocates attention** to regions of uncertainty
3. **Generates queries** to reduce prediction error
4. **Couples** with neighbors to share information
5. **Evolves** through attractor dynamics in semantic space

The result is a **tissue of meaning** — thousands of cells packed together, each with internal structure (spin), communicating through boundaries (couplings), organized into basins of attraction (semantic domains).

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         SEMANTIC CELL SYSTEM                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                        ONTOLOGY LAYER                                │   │
│  │  Level 0: ~200 Primitives (ENTITY, CAUSE, GOOD, NOW, etc.)          │   │
│  │  Level 1: ~2,000 Basic (ANIMAL, EMOTION, TOOL, PLACE, etc.)         │   │
│  │  Level 2: ~6,000 Common (DOG, HAPPINESS, HAMMER, PARIS, etc.)       │   │
│  │  ─────────────────────────────────────────────────────────────────  │   │
│  │  Total: ~8,000+ cells (expandable to 20,000+)                       │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                    │                                        │
│                                    ▼                                        │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                     GENERATIVE MODEL (per cell)                      │   │
│  │                                                                      │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐                  │   │
│  │  │  Temporal   │  │  Neighbor   │  │ Perturbation│                  │   │
│  │  │   Model     │  │   Model     │  │    Model    │                  │   │
│  │  │             │  │             │  │             │                  │   │
│  │  │ Self-dyna-  │  │ Coupling    │  │ External    │                  │   │
│  │  │ mics pred-  │  │ influence   │  │ world       │                  │   │
│  │  │ iction      │  │ from neigh- │  │ perturba-   │                  │   │
│  │  │             │  │ bors        │  │ tions       │                  │   │
│  │  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘                  │   │
│  │         │                │                │                          │   │
│  │         └────────────────┼────────────────┘                          │   │
│  │                          ▼                                           │   │
│  │                   ┌─────────────┐                                    │   │
│  │                   │ PREDICTION  │                                    │   │
│  │                   │ P̂(t+1) =    │                                    │   │
│  │                   │ f(temporal) │                                    │   │
│  │                   │ + neighbor  │                                    │   │
│  │                   │ + external  │                                    │   │
│  │                   └──────┬──────┘                                    │   │
│  │                          │                                           │   │
│  │                          ▼                                           │   │
│  │         ┌────────────────────────────────┐                           │   │
│  │         │      PREDICTION ERROR          │                           │   │
│  │         │      ε = P̂(t+1) - P(t+1)       │                           │   │
│  │         └────────────────┬───────────────┘                           │   │
│  │                          │                                           │   │
│  │              ┌───────────┴───────────┐                               │   │
│  │              ▼                       ▼                               │   │
│  │    ┌─────────────────┐    ┌─────────────────┐                        │   │
│  │    │ ATTENTION       │    │ MODEL UPDATE    │                        │   │
│  │    │ ALLOCATION      │    │                 │                        │   │
│  │    │                 │    │ Gradient descent│                        │   │
│  │    │ Focus on high-  │    │ on prediction   │                        │   │
│  │    │ uncertainty     │    │ error           │                        │   │
│  │    │ regions         │    │                 │                        │   │
│  │    └────────┬────────┘    └─────────────────┘                        │   │
│  │             │                                                        │   │
│  │             ▼                                                        │   │
│  │    ┌─────────────────┐                                               │   │
│  │    │ QUERY           │                                               │   │
│  │    │ GENERATION      │                                               │   │
│  │    │                 │                                               │   │
│  │    │ "What is the    │                                               │   │
│  │    │  state of X?"   │                                               │   │
│  │    └─────────────────┘                                               │   │
│  │                                                                      │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                        BASIN DYNAMICS                                │   │
│  │                                                                      │   │
│  │   ENTITY ──────┐    EVENT ───────┐    PROPERTY ──────┐              │   │
│  │   basin        │    basin        │    basin          │              │   │
│  │     ◉ DOG      │      ◉ RUNNING  │      ◉ RED        │              │   │
│  │    ◉ CAT       │     ◉ EATING    │     ◉ FAST        │              │   │
│  │   ◉ PERSON     │    ◉ SLEEPING   │    ◉ HEAVY        │              │   │
│  │                │                 │                   │              │   │
│  │   Cells settle into basins of attraction based on semantic type     │   │
│  │   Phase transitions occur when meaning shifts between domains       │   │
│  │                                                                      │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Core Data Structures

### 1. Semantic Cell (Python)

```python
@dataclass
class SemanticCell:
    id: str                    # Unique identifier
    name: str                  # Human-readable name
    description: str           # What this concept means
    level: CellLevel           # PRIMITIVE, BASIC, or COMMON
    domain: str                # Category (ANIMAL, EMOTION, etc.)
    basin: BasinType           # Attractor type (ENTITY, EVENT, etc.)
    state: CellState           # Current dynamic state
    parent_id: Optional[str]   # Hierarchical parent
    children_ids: List[str]    # Hierarchical children
    coupling_ids: List[str]    # Connected cells
```

### 2. Cell State (Dynamic)

```python
@dataclass
class CellState:
    position: List[float]      # 512-dim embedding position
    velocity: List[float]      # Rate of change
    acceleration: List[float]  # Second derivative
    spin: List[float]          # 3D attention direction
    grade: float               # Confidence (0-1)
    energy: float              # Activation level (0-1)
```

### 3. Generative Model (Haskell)

```haskell
data GenerativeModel = GenerativeModel
    { gmTemporal     :: TemporalModel      -- Self-dynamics predictor
    , gmNeighbor     :: NeighborModel      -- Neighbor influence
    , gmPerturbation :: PerturbationModel  -- External world
    , gmDimension    :: Int                -- Embedding dimension
    , gmModelVersion :: Int                -- Update counter
    , gmTrainedOn    :: Int                -- Training count
    }
```

### 4. Coupling

```python
@dataclass
class Coupling:
    id: str
    source_id: str
    target_id: str
    coupling_type: CouplingType  # IS_A, HAS, CAUSES, SIMILAR, etc.
    strength: float              # 0-1
    bidirectional: bool
```

---

## Ontology Structure

### Level 0: Primitives (~200 cells)
Fundamental building blocks that cannot be decomposed further.

| Category | Examples |
|----------|----------|
| **Existence** | ENTITY, THING, BEING, EXISTENCE |
| **Causation** | CAUSE, EFFECT, ENABLE, PREVENT |
| **Temporal** | BEFORE, AFTER, NOW, DURATION |
| **Spatial** | HERE, THERE, NEAR, FAR, IN, ON |
| **Quality** | GOOD, BAD, MORE, LESS, SAME |
| **Logic** | AND, OR, NOT, IF, ALL, SOME |
| **Agency** | AGENT, PATIENT, INSTRUMENT |
| **Modal** | POSSIBLE, NECESSARY, ACTUAL |

### Level 1: Basic (~2,000 cells)
Common categories that most humans learn.

| Domain | Examples |
|--------|----------|
| **Animals** | MAMMAL, BIRD, FISH, INSECT |
| **Plants** | TREE, FLOWER, GRASS, VEGETABLE |
| **Objects** | TOOL, CONTAINER, VEHICLE, FURNITURE |
| **Places** | BUILDING, ROOM, LANDSCAPE, CITY |
| **Actions** | MOVE, MAKE, GIVE, TAKE, THINK |
| **Properties** | COLOR, SIZE, SHAPE, TEXTURE |
| **Relations** | PART_OF, CONTAINS, NEAR, SIMILAR |
| **Events** | BIRTH, DEATH, MEETING, CONFLICT |
| **Emotions** | JOY, SADNESS, FEAR, ANGER, LOVE |
| **Social** | FAMILY, FRIEND, GROUP, ROLE |

### Level 2: Common (~6,000+ cells)
Specific concepts most educated adults know.

| Domain | Count | Examples |
|--------|-------|----------|
| **Animals** | ~350 | DOG, LABRADOR, EAGLE, SALMON, BUTTERFLY |
| **Plants** | ~200 | OAK, ROSE, TOMATO, APPLE, BASIL |
| **Food** | ~200 | BREAD, PASTA, STEAK, CHEESE, CAKE |
| **Tools** | ~150 | HAMMER, SCREWDRIVER, KNIFE, SHOVEL |
| **Places** | ~250 | HOUSE, OFFICE, PARK, MOUNTAIN, OCEAN |
| **Activities** | ~200 | RUNNING, COOKING, READING, DANCING |
| **Emotions** | ~150 | HAPPINESS, GRIEF, ANXIETY, LOVE |
| **Social** | ~150 | MARRIAGE, FRIENDSHIP, TEAMWORK |
| **Technology** | ~200 | COMPUTER, SMARTPHONE, INTERNET |
| **Science** | ~200 | ATOM, GRAVITY, EVOLUTION, DNA |
| **Art** | ~200 | PAINTING, SCULPTURE, PHOTOGRAPHY |
| **Music** | ~250 | JAZZ, GUITAR, MELODY, RHYTHM |
| **Medicine** | ~200 | DISEASE, SURGERY, MEDICATION |
| **Law** | ~150 | CONTRACT, TRIAL, VERDICT |
| **Business** | ~200 | COMPANY, PROFIT, INVESTMENT |
| **Geography** | ~250 | CONTINENT, COUNTRY, CITY, MOUNTAIN |
| **History** | ~150 | WAR, REVOLUTION, EMPIRE |
| **Religion** | ~150 | CHRISTIANITY, PRAYER, TEMPLE |
| **Materials** | ~150 | METAL, WOOD, PLASTIC, FABRIC |
| **Weather** | ~100 | RAIN, SNOW, HURRICANE, CLIMATE |
| **Measurement** | ~100 | METER, KILOGRAM, CELSIUS |
| **Games** | ~150 | CHESS, POKER, VIDEO_GAME |

---

## Prediction System

Each cell predicts its own future at 4 time horizons:

| Horizon | Duration | Use Case |
|---------|----------|----------|
| **Immediate** | 10ms | Real-time perception |
| **Short-term** | 1 minute | Conversation context |
| **Medium-term** | 1 hour | Task completion |
| **Long-term** | 1 day | Learning, memory consolidation |

### Prediction Formula

```
P̂(t+1) = temporal_prediction + neighbor_influence + external_perturbation

where:
  temporal_prediction = tanh(W_h · [P(t), V(t)] + b_h)
  neighbor_influence = Σ coupling[j] × attention[j] × (neighbor[j] - self)
  external_perturbation = expected_magnitude × expected_direction
```

---

## Attention Allocation

Cells allocate attention to regions with high **expected information gain**:

```
EIG(region) = uncertainty(region) × relevance(region)

where:
  uncertainty = variance of predictions in that region
  relevance = exp(-distance / influence_radius)
```

This implements **active inference** — cells actively seek information to reduce prediction error.

---

## Visualization

The system renders as **biological tissue**:

```
┌─────────────────────────────────────────────────────────────────┐
│                                                                 │
│   Each cell has:                                                │
│   • COLOR = position in embedding space (projected to RGB)     │
│   • SPIN = radial lines showing attention direction            │
│   • NUCLEUS = dark center point                                │
│   • BOUNDARY = green edge showing coupling strength            │
│                                                                 │
│   ┌──────┐ ┌──────┐ ┌──────┐                                   │
│   │  ✳   │ │  ✳   │ │  ✳   │                                   │
│   │ ╱│╲  │ │ ╱│╲  │ │ ╱│╲  │  ← Radial spin pattern           │
│   │╱ │ ╲ │ │╱ │ ╲ │ │╱ │ ╲ │                                   │
│   └──┼───┘ └──┼───┘ └──┼───┘                                   │
│      │        │        │                                       │
│   ┌──┼───┐ ┌──┼───┐ ┌──┼───┐  ← Green edges = coupling        │
│   │  ✳   │ │  ✳   │ │  ✳   │                                   │
│   │ ╱│╲  │ │ ╱│╲  │ │ ╱│╲  │                                   │
│   └──────┘ └──────┘ └──────┘                                   │
│                                                                 │
│   Basin boundaries show phase transition zones                  │
│   (where cells are deciding which attractor to fall into)      │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## File Structure

```
semantic-cells/
├── src/
│   ├── core/
│   │   └── types.py                    # Core data structures
│   │
│   ├── ontology/
│   │   ├── level0_primitives.py        # ~200 primitive cells
│   │   ├── level1_basic.py             # ~2,000 basic cells
│   │   ├── level2_common.py            # ~700 common cells
│   │   ├── level2_expansions_part2.py  # ~1,000 objects/places
│   │   ├── level2_expansions_part3.py  # ~800 emotions/tech
│   │   ├── level2_expansions_part4.py  # ~1,300 art/music/law
│   │   └── ontology_assembler.py       # Master assembly
│   │
│   └── visualization/
│       └── cell_renderer.py            # SVG tissue renderer
│
├── output/
│   └── semantic_tissue.svg             # Sample visualization
│
└── data/
    └── ontology.json                   # Exported ontology

engram-attestation/
└── engram-types/
    └── src/
        └── Engram/
            └── Predictive/
                └── Model.hs            # Generative model (Haskell)
```

---

## Current Status

| Component | Status | Details |
|-----------|--------|---------|
| **Core Types** | ✅ Complete | Python dataclasses for cells, couplings, state |
| **Level 0 Ontology** | ✅ Complete | ~200 primitive cells |
| **Level 1 Ontology** | ✅ Complete | ~2,000 basic cells |
| **Level 2 Ontology** | ✅ Complete | ~6,000 common cells |
| **Generative Model** | ✅ Complete | Haskell implementation |
| **Visualization** | ✅ Complete | SVG tissue renderer |
| **Ontology Assembler** | ✅ Complete | Combines all levels |
| **Cell Initialization** | ⏳ Pending | Instantiate cells from ontology |
| **Agent Foraging** | ⏳ Pending | Active information seeking |
| **Database Layer** | ⏳ Pending | Persistence and retrieval |
| **Synchronization** | ⏳ Pending | Multi-cell coordination |
| **Haskell-Python Bridge** | ⏳ Pending | Connect model to cells |

---

## Next Steps

### Phase 1: Cell Instantiation
1. Load ontology into memory
2. Initialize cell positions (deterministic from hash)
3. Set up coupling network
4. Assign cells to basins

### Phase 2: Dynamics Engine
1. Implement prediction loop (10ms tick)
2. Compute prediction errors
3. Update attention allocation
4. Apply basin dynamics

### Phase 3: Query System
1. Generate queries from high-error cells
2. Route queries to information sources
3. Update cells with new observations
4. Propagate updates through couplings

### Phase 4: Integration
1. Bridge Haskell model to Python runtime
2. Connect to external LLM for query resolution
3. Build database persistence layer
4. Implement synchronization rhythms (gamma, theta, etc.)

### Phase 5: Scaling
1. Expand to 20,000+ cells
2. Add domain-specific ontologies
3. Implement distributed computation
4. Build user-specific memory layers

---

## Key Insights

### 1. Cells are Predictive Agents
Not passive embeddings, but active predictors that maintain beliefs about their own evolution.

### 2. Attention is Resource Allocation
Cells compete for limited attention based on uncertainty × relevance.

### 3. Error Drives Learning
Prediction error is the signal for both attention allocation and model updates.

### 4. Basins Create Structure
Attractor dynamics naturally organize concepts into semantic categories.

### 5. Couplings Enable Communication
Information flows between cells through coupling strengths modulated by attention.

### 6. The Tissue is Alive
The visualization shows a living system — each cell with internal spin, boundaries with neighbors, phase transitions at basin edges.

---

## Theoretical Foundation

This architecture draws from:

- **Active Inference** (Friston): Free energy minimization through prediction and action
- **Predictive Processing** (Clark): Brain as prediction machine
- **Attractor Dynamics** (Hopfield): Memory as stable patterns
- **Geometric Algebra** (Hestenes): Unified framework for transformations
- **Category Theory**: Compositional semantics through functors

The result is a **semantically grounded, dynamically evolving, attention-allocating** system for representing meaning — not as static vectors, but as living tissue.

---

## Conclusion

We have built the foundation for a **semantic cell system** with:

- **~8,000 cells** across 3 levels of abstraction
- **Generative models** for each cell (temporal, neighbor, perturbation)
- **Prediction at 4 horizons** (10ms to 1 day)
- **Attention allocation** based on expected information gain
- **Basin dynamics** for semantic organization
- **Visualization** as biological tissue

The next phase is to bring this tissue to life — running the prediction loops, generating queries, and watching the semantic network evolve.

This is not just a knowledge graph. This is a **living system of meaning**.
