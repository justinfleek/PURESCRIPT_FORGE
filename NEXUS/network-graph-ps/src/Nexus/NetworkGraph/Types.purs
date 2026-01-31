module Nexus.NetworkGraph.Types where

import Prelude

import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, (.:), (.:?))
import Data.Either (Either(..))
import Data.Map as Map

-- | Node type
data NodeType = Agent | Concept | Entity | Content

derive instance eqNodeType :: Eq NodeType
derive instance ordNodeType :: Ord NodeType

instance encodeJsonNodeType :: EncodeJson NodeType where
  encodeJson = case _ of
    Agent -> encodeJson "agent"
    Concept -> encodeJson "concept"
    Entity -> encodeJson "entity"
    Content -> encodeJson "content"

instance decodeJsonNodeType :: DecodeJson NodeType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "agent" -> pure Agent
      "concept" -> pure Concept
      "entity" -> pure Entity
      "content" -> pure Content
      _ -> Left "Invalid node type"

-- | Edge type
data EdgeType = AgentAgent | AgentConcept | ConceptConcept | EntityEntity | ContentConcept

derive instance eqEdgeType :: Eq EdgeType
derive instance ordEdgeType :: Ord EdgeType

instance encodeJsonEdgeType :: EncodeJson EdgeType where
  encodeJson = case _ of
    AgentAgent -> encodeJson "agent-agent"
    AgentConcept -> encodeJson "agent-concept"
    ConceptConcept -> encodeJson "concept-concept"
    EntityEntity -> encodeJson "entity-entity"
    ContentConcept -> encodeJson "content-concept"

instance decodeJsonEdgeType :: DecodeJson EdgeType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "agent-agent" -> pure AgentAgent
      "agent-concept" -> pure AgentConcept
      "concept-concept" -> pure ConceptConcept
      "entity-entity" -> pure EntityEntity
      "content-concept" -> pure ContentConcept
      _ -> Left "Invalid edge type"

-- | Network node
type Node =
  { id :: String
  , nodeType :: NodeType
  , label :: String
  , properties :: Json
  }

instance encodeJsonNode :: EncodeJson Node where
  encodeJson n = encodeJson
    { id: n.id
    , nodeType: n.nodeType
    , label: n.label
    , properties: n.properties
    }

instance decodeJsonNode :: DecodeJson Node where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    nodeType <- obj .: "nodeType"
    label <- obj .: "label"
    properties <- obj .: "properties"
    pure { id, nodeType, label, properties }

-- | Network edge
type Edge =
  { id :: String
  , sourceId :: String
  , targetId :: String
  , edgeType :: EdgeType
  , weight :: Number
  , properties :: Json
  }

instance encodeJsonEdge :: EncodeJson Edge where
  encodeJson e = encodeJson
    { id: e.id
    , sourceId: e.sourceId
    , targetId: e.targetId
    , edgeType: e.edgeType
    , weight: e.weight
    , properties: e.properties
    }

instance decodeJsonEdge :: DecodeJson Edge where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    sourceId <- obj .: "sourceId"
    targetId <- obj .: "targetId"
    edgeType <- obj .: "edgeType"
    weight <- obj .: "weight"
    properties <- obj .: "properties"
    pure { id, sourceId, targetId, edgeType, weight, properties }

-- | Network graph
type NetworkGraph =
  { nodes :: Map.Map String Node
  , edges :: Map.Map String Edge
  }

instance encodeJsonNetworkGraph :: EncodeJson NetworkGraph where
  encodeJson g = encodeJson
    { nodes: Map.values g.nodes
    , edges: Map.values g.edges
    }

instance decodeJsonNetworkGraph :: DecodeJson NetworkGraph where
  decodeJson json = do
    obj <- decodeJson json
    nodesArray <- obj .: "nodes"
    edgesArray <- obj .: "edges"
    
    -- Convert arrays to maps
    let nodes = Map.fromFoldable $ map (\n -> n.id /\ n) nodesArray
    let edges = Map.fromFoldable $ map (\e -> e.id /\ e) edgesArray
    
    pure { nodes, edges }
