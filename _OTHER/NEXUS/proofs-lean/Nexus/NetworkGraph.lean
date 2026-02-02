-- | NEXUS Network Graph Consistency Proofs
-- | Mathematically proven properties about network graphs
-- |
-- | Strategy: Encode graph operations that maintain invariants by construction.
-- | Invariant-preserving operations are the only way to build graphs.

import Lean
import Std.Data.List.Lemmas

-- | Node ID
structure NodeId where
  id : String
  deriving DecidableEq, BEq, Repr

-- | Edge ID
structure EdgeId where
  id : String
  deriving DecidableEq, BEq, Repr

-- | Network node
structure Node where
  id : NodeId
  nodeType : String
  label : String
  deriving DecidableEq, Repr

-- | Network edge with validated weight
structure Edge where
  id : EdgeId
  sourceId : NodeId
  targetId : NodeId
  weight : Float
  h_weight_lower : 0.0 ≤ weight := by native_decide
  h_weight_upper : weight ≤ 1.0 := by native_decide
  h_no_self_loop : sourceId ≠ targetId := by decide
  deriving Repr

-- | BEq instance for Edge (ignoring proofs)
instance : BEq Edge where
  beq e1 e2 := e1.id == e2.id && e1.sourceId == e2.sourceId &&
               e1.targetId == e2.targetId && e1.weight == e2.weight

-- | Network graph with consistency invariant encoded in type
-- | The invariant: every edge's source and target must exist in nodes
structure NetworkGraph where
  nodes : List Node
  edges : List Edge
  h_consistent : ∀ e ∈ edges,
    (∃ n ∈ nodes, n.id = e.sourceId) ∧
    (∃ n ∈ nodes, n.id = e.targetId)

/-!
## Graph Construction

We provide smart constructors that maintain invariants by construction.
-/

-- | Empty graph (trivially consistent)
def emptyGraph : NetworkGraph where
  nodes := []
  edges := []
  h_consistent := by intro e h; exact False.elim (List.not_mem_nil e h)

-- | Add a node to the graph (preserves consistency)
def addNode (graph : NetworkGraph) (node : Node) : NetworkGraph where
  nodes := node :: graph.nodes
  edges := graph.edges
  h_consistent := by
    intro e h_e
    have ⟨h_source, h_target⟩ := graph.h_consistent e h_e
    constructor
    · obtain ⟨n, h_n_mem, h_n_eq⟩ := h_source
      exact ⟨n, List.mem_cons_of_mem node h_n_mem, h_n_eq⟩
    · obtain ⟨n, h_n_mem, h_n_eq⟩ := h_target
      exact ⟨n, List.mem_cons_of_mem node h_n_mem, h_n_eq⟩

-- | Check if a node exists in the graph
def hasNode (graph : NetworkGraph) (nodeId : NodeId) : Bool :=
  graph.nodes.any (·.id == nodeId)

-- | Lemma: hasNode returns true iff node exists
lemma hasNode_iff (graph : NetworkGraph) (nodeId : NodeId) :
  hasNode graph nodeId = true ↔ ∃ n ∈ graph.nodes, n.id = nodeId := by
  unfold hasNode
  simp [List.any_eq_true]
  constructor
  · intro ⟨n, h_mem, h_eq⟩
    exact ⟨n, h_mem, beq_eq_true_iff_eq.mp h_eq⟩
  · intro ⟨n, h_mem, h_eq⟩
    exact ⟨n, h_mem, beq_eq_true_iff_eq.mpr h_eq⟩

-- | Add an edge with validation (returns Option for safety)
def addEdge (graph : NetworkGraph) (edge : Edge)
  (h_source : ∃ n ∈ graph.nodes, n.id = edge.sourceId)
  (h_target : ∃ n ∈ graph.nodes, n.id = edge.targetId) : NetworkGraph where
  nodes := graph.nodes
  edges := edge :: graph.edges
  h_consistent := by
    intro e h_e
    cases List.mem_cons.mp h_e with
    | inl h_eq =>
      rw [h_eq]
      exact ⟨h_source, h_target⟩
    | inr h_in_old =>
      exact graph.h_consistent e h_in_old

-- | Try to add an edge (returns Option)
def tryAddEdge (graph : NetworkGraph) (edge : Edge) : Option NetworkGraph :=
  if h_source : ∃ n ∈ graph.nodes, n.id = edge.sourceId then
    if h_target : ∃ n ∈ graph.nodes, n.id = edge.targetId then
      some (addEdge graph edge h_source h_target)
    else
      none
  else
    none

/-!
## Proven Properties

All properties follow mathematically from the type-level invariants.
-/

-- | Theorem: Graph consistency is always maintained
-- | This is immediate from the type - h_consistent is required for any NetworkGraph
theorem graph_consistency (graph : NetworkGraph) :
  ∀ e ∈ graph.edges,
    (∃ n ∈ graph.nodes, n.id = e.sourceId) ∧
    (∃ n ∈ graph.nodes, n.id = e.targetId) := graph.h_consistent

-- | Theorem: All edge weights are bounded
-- | This is immediate from the Edge type's h_weight_lower and h_weight_upper
theorem edge_weight_bounds (graph : NetworkGraph) :
  ∀ e ∈ graph.edges, 0.0 ≤ e.weight ∧ e.weight ≤ 1.0 := by
  intro e _
  exact ⟨e.h_weight_lower, e.h_weight_upper⟩

-- | Theorem: No self-loops
-- | This is immediate from the Edge type's h_no_self_loop
theorem no_self_loops (graph : NetworkGraph) :
  ∀ e ∈ graph.edges, e.sourceId ≠ e.targetId := by
  intro e _
  exact e.h_no_self_loop

-- | Theorem: Adding a node preserves all edges
theorem add_node_preserves_edges (graph : NetworkGraph) (node : Node) :
  (addNode graph node).edges = graph.edges := rfl

-- | Theorem: Adding a node increases node count
theorem add_node_increases_nodes (graph : NetworkGraph) (node : Node) :
  (addNode graph node).nodes.length = graph.nodes.length + 1 := by
  simp [addNode]

-- | Theorem: New node is in graph after adding
theorem new_node_in_graph (graph : NetworkGraph) (node : Node) :
  node ∈ (addNode graph node).nodes := by
  simp [addNode]

-- | Theorem: Existing nodes preserved after adding new node
theorem existing_nodes_preserved (graph : NetworkGraph) (node newNode : Node) :
  node ∈ graph.nodes → node ∈ (addNode graph newNode).nodes := by
  intro h
  simp [addNode, h]

-- | Theorem: Empty graph has no edges
theorem empty_graph_no_edges : emptyGraph.edges = [] := rfl

-- | Theorem: Empty graph has no nodes
theorem empty_graph_no_nodes : emptyGraph.nodes = [] := rfl

-- | Theorem: tryAddEdge succeeds iff both endpoints exist
theorem tryAddEdge_succeeds_iff (graph : NetworkGraph) (edge : Edge) :
  (tryAddEdge graph edge).isSome = true ↔
    (∃ n ∈ graph.nodes, n.id = edge.sourceId) ∧
    (∃ n ∈ graph.nodes, n.id = edge.targetId) := by
  unfold tryAddEdge
  constructor
  · intro h
    simp only [Option.isSome_iff_exists] at h
    split at h <;> simp_all
    split at h <;> simp_all
  · intro ⟨h_source, h_target⟩
    simp [h_source, h_target]

-- | Theorem: Subgraph relation - if edges are subset, consistency preserved
theorem subgraph_consistent (graph : NetworkGraph) (edges' : List Edge)
  (h_subset : ∀ e ∈ edges', e ∈ graph.edges) :
  ∀ e ∈ edges',
    (∃ n ∈ graph.nodes, n.id = e.sourceId) ∧
    (∃ n ∈ graph.nodes, n.id = e.targetId) := by
  intro e h_e
  exact graph.h_consistent e (h_subset e h_e)

