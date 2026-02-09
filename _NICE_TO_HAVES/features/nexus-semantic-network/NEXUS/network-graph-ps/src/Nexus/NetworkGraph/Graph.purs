module Nexus.NetworkGraph.Graph where

import Prelude

import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Nexus.NetworkGraph.Types (Node, Edge, NetworkGraph, NodeType, EdgeType)

-- | Create empty network graph
emptyGraph :: NetworkGraph
emptyGraph = { nodes: Map.empty, edges: Map.empty }

-- | Add node to graph
addNode :: NetworkGraph -> Node -> Either String NetworkGraph
addNode graph node = do
  -- Validate node ID is not empty
  if node.id == "" then
    Left "Node ID cannot be empty"
  else
    Right $ graph { nodes = Map.insert node.id node graph.nodes }

-- | Remove node and its edges
removeNode :: NetworkGraph -> String -> NetworkGraph
removeNode graph nodeId =
  { nodes: Map.delete nodeId graph.nodes
  , edges: Map.filter (\e -> e.sourceId /= nodeId && e.targetId /= nodeId) graph.edges
  }

-- | Get node by ID
getNode :: NetworkGraph -> String -> Maybe Node
getNode graph nodeId = Map.lookup nodeId graph.nodes

-- | Add edge to graph
addEdge :: NetworkGraph -> Edge -> Either String NetworkGraph
addEdge graph edge = do
  -- Validate source and target nodes exist
  sourceNode <- case getNode graph edge.sourceId of
    Nothing -> Left $ "Source node not found: " <> edge.sourceId
    Just n -> Right n
  
  targetNode <- case getNode graph edge.targetId of
    Nothing -> Left $ "Target node not found: " <> edge.targetId
    Just n -> Right n
  
  -- Validate edge ID is not empty
  if edge.id == "" then
    Left "Edge ID cannot be empty"
  else
    -- Validate weight is in [0, 1]
    if edge.weight < 0.0 || edge.weight > 1.0 then
      Left "Edge weight must be in [0.0, 1.0]"
    else
      -- Validate source != target
      if edge.sourceId == edge.targetId then
        Left "Edge source and target cannot be the same"
      else
        Right $ graph { edges = Map.insert edge.id edge graph.edges }

-- | Remove edge from graph
removeEdge :: NetworkGraph -> String -> NetworkGraph
removeEdge graph edgeId =
  graph { edges = Map.delete edgeId graph.edges }

-- | Get edge by ID
getEdge :: NetworkGraph -> String -> Maybe Edge
getEdge graph edgeId = Map.lookup edgeId graph.edges

-- | Get neighbors of a node
getNeighbors :: NetworkGraph -> String -> Array Node
getNeighbors graph nodeId =
  let
    outgoing = Map.values $ Map.filter (\e -> e.sourceId == nodeId) graph.edges
    incoming = Map.values $ Map.filter (\e -> e.targetId == nodeId) graph.edges
    neighborIds = Set.fromFoldable $
      (map _.targetId outgoing) <> (map _.sourceId incoming)
  in
    Array.mapMaybe (\id -> getNode graph id) (Set.toUnfoldable neighborIds)

-- | Get edges for a node
getNodeEdges :: NetworkGraph -> String -> Array Edge
getNodeEdges graph nodeId =
  Map.values $ Map.filter (\e -> e.sourceId == nodeId || e.targetId == nodeId) graph.edges

-- | Get nodes by type
getNodesByType :: NetworkGraph -> NodeType -> Array Node
getNodesByType graph nodeType =
  Array.filter (\n -> n.nodeType == nodeType) (Map.values graph.nodes)

-- | Get edges by type
getEdgesByType :: NetworkGraph -> EdgeType -> Array Edge
getEdgesByType graph edgeType =
  Array.filter (\e -> e.edgeType == edgeType) (Map.values graph.edges)

-- | Count nodes
nodeCount :: NetworkGraph -> Int
nodeCount graph = Map.size graph.nodes

-- | Count edges
edgeCount :: NetworkGraph -> Int
edgeCount graph = Map.size graph.edges
