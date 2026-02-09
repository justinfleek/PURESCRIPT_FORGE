{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Network Graph Metrics
-- | Performance-critical metrics calculations
module Nexus.NetworkGraph.Metrics where

{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Network Graph Metrics
-- | Performance-critical metrics calculations
module Nexus.NetworkGraph.Metrics where

import Prelude hiding (head, tail, fromJust)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')
import Data.Foldable (foldMap)

-- | Node ID
type NodeId = String

-- | Edge weight
type Weight = Double

-- | Edge
data Edge = Edge
  { edgeSourceId :: NodeId
  , edgeTargetId :: NodeId
  , edgeWeight :: Weight
  }
  deriving (Show, Eq, Ord)

-- | Network graph
data NetworkGraph = NetworkGraph
  { graphNodes :: Set NodeId
  , graphEdges :: Map (NodeId, NodeId) Edge
  }
  deriving (Show, Eq)

-- | Calculate degree centrality for a node
degreeCentrality :: NetworkGraph -> NodeId -> Double
degreeCentrality graph nodeId =
  let
    totalNodes = fromIntegral $ Set.size (graphNodes graph)
    neighborCount = fromIntegral $ countNeighbors graph nodeId
  in
    if totalNodes <= 1 then
      0.0
    else
      neighborCount / (totalNodes - 1.0)

-- | Count neighbors of a node
countNeighbors :: NetworkGraph -> NodeId -> Int
countNeighbors graph nodeId =
  let
    outgoing = Map.filter (\e -> edgeSourceId e == nodeId) (graphEdges graph)
    incoming = Map.filter (\e -> edgeTargetId e == nodeId) (graphEdges graph)
    neighborSet = Set.fromList $
      (map edgeTargetId $ Map.elems outgoing) <>
      (map edgeSourceId $ Map.elems incoming)
  in
    Set.size neighborSet

-- | Calculate clustering coefficient for a node
clusteringCoefficient :: NetworkGraph -> NodeId -> Double
clusteringCoefficient graph nodeId =
  let
    neighbors = getNeighbors graph nodeId
    neighborCount = length neighbors
  in
    if neighborCount < 2 then
      0.0
    else
      let
        edgesBetweenNeighbors = countEdgesBetween graph neighbors
        possibleEdges = neighborCount * (neighborCount - 1) `div` 2
      in
        if possibleEdges == 0 then
          0.0
        else
          fromIntegral edgesBetweenNeighbors / fromIntegral possibleEdges

-- | Get neighbors of a node
getNeighbors :: NetworkGraph -> NodeId -> [NodeId]
getNeighbors graph nodeId =
  let
    outgoing = Map.filter (\e -> edgeSourceId e == nodeId) (graphEdges graph)
    incoming = Map.filter (\e -> edgeTargetId e == nodeId) (graphEdges graph)
  in
    Set.toList $ Set.fromList $
      (map edgeTargetId $ Map.elems outgoing) <>
      (map edgeSourceId $ Map.elems incoming)

-- | Count edges between neighbors
countEdgesBetween :: NetworkGraph -> [NodeId] -> Int
countEdgesBetween graph neighbors =
  let
    neighborSet = Set.fromList neighbors
    edges = Map.elems $ Map.filter (\e ->
      Set.member (edgeSourceId e) neighborSet &&
      Set.member (edgeTargetId e) neighborSet
    ) (graphEdges graph)
    edgeCount = length edges
  in
    edgeCount `div` 2  -- Divide by 2 for undirected graph

-- | Calculate average clustering coefficient
averageClusteringCoefficient :: NetworkGraph -> Double
averageClusteringCoefficient graph =
  let
    nodes = Set.toList (graphNodes graph)
    coefficients = map (clusteringCoefficient graph) nodes
    total = sum coefficients
    count = length coefficients
  in
    if count == 0 then
      0.0
    else
      total / fromIntegral count

-- | Calculate network density
networkDensity :: NetworkGraph -> Double
networkDensity graph =
  let
    nodeCount = Set.size (graphNodes graph)
    edgeCount = Map.size (graphEdges graph)
    possibleEdges = nodeCount * (nodeCount - 1) `div` 2
  in
    if possibleEdges == 0 then
      0.0
    else
      fromIntegral edgeCount / fromIntegral possibleEdges
