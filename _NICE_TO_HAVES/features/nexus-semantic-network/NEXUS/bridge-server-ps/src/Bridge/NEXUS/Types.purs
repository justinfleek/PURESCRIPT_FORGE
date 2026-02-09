module Bridge.NEXUS.Types where

import Prelude

import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, (.:), (.:?))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))

-- | Agent type
data AgentType = WebSearch | ContentExtraction | NetworkFormation | DatabaseLayer

derive instance eqAgentType :: Eq AgentType
derive instance ordAgentType :: Ord AgentType

instance encodeJsonAgentType :: EncodeJson AgentType where
  encodeJson = case _ of
    WebSearch -> encodeJson "web_search"
    ContentExtraction -> encodeJson "content_extraction"
    NetworkFormation -> encodeJson "network_formation"
    DatabaseLayer -> encodeJson "database_layer"

instance decodeJsonAgentType :: DecodeJson AgentType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "web_search" -> pure WebSearch
      "content_extraction" -> pure ContentExtraction
      "network_formation" -> pure NetworkFormation
      "database_layer" -> pure DatabaseLayer
      _ -> Left "Invalid agent type"

-- | Agent status
data AgentStatus = Running | Stopped | Error

derive instance eqAgentStatus :: Eq AgentStatus
derive instance ordAgentStatus :: Ord AgentStatus

instance encodeJsonAgentStatus :: EncodeJson AgentStatus where
  encodeJson = case _ of
    Running -> encodeJson "running"
    Stopped -> encodeJson "stopped"
    Error -> encodeJson "error"

instance decodeJsonAgentStatus :: DecodeJson AgentStatus where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "running" -> pure Running
      "stopped" -> pure Stopped
      "error" -> pure Error
      _ -> Left "Invalid agent status"

-- | Agent launch response
type AgentLaunchResponse =
  { success :: Boolean
  , agentId :: String
  }

instance encodeJsonAgentLaunchResponse :: EncodeJson AgentLaunchResponse where
  encodeJson r = encodeJson
    { success: r.success
    , agentId: r.agentId
    }

instance decodeJsonAgentLaunchResponse :: DecodeJson AgentLaunchResponse where
  decodeJson json = do
    obj <- decodeJson json
    success <- obj .: "success"
    agentId <- obj .: "agentId"
    pure { success, agentId }

-- | Agent status response
type AgentStatusResponse =
  { agentId :: String
  , status :: AgentStatus
  , startedAt :: Maybe String
  }

instance encodeJsonAgentStatusResponse :: EncodeJson AgentStatusResponse where
  encodeJson r = encodeJson
    { agentId: r.agentId
    , status: r.status
    , startedAt: r.startedAt
    }

instance decodeJsonAgentStatusResponse :: DecodeJson AgentStatusResponse where
  decodeJson json = do
    obj <- decodeJson json
    agentId <- obj .: "agentId"
    status <- obj .: "status"
    startedAt <- obj .:? "startedAt"
    pure { agentId, status, startedAt }

-- | Network node
type NetworkNode =
  { id :: String
  , label :: String
  , nodeType :: String
  , properties :: Json
  }

instance encodeJsonNetworkNode :: EncodeJson NetworkNode where
  encodeJson n = encodeJson
    { id: n.id
    , label: n.label
    , nodeType: n.nodeType
    , properties: n.properties
    }

instance decodeJsonNetworkNode :: DecodeJson NetworkNode where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    label <- obj .: "label"
    nodeType <- obj .: "nodeType"
    properties <- obj .: "properties"
    pure { id, label, nodeType, properties }

-- | Network edge
type NetworkEdge =
  { id :: String
  , sourceId :: String
  , targetId :: String
  , weight :: Number
  , properties :: Json
  }

instance encodeJsonNetworkEdge :: EncodeJson NetworkEdge where
  encodeJson e = encodeJson
    { id: e.id
    , sourceId: e.sourceId
    , targetId: e.targetId
    , weight: e.weight
    , properties: e.properties
    }

instance decodeJsonNetworkEdge :: DecodeJson NetworkEdge where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    sourceId <- obj .: "sourceId"
    targetId <- obj .: "targetId"
    weight <- obj .: "weight"
    properties <- obj .: "properties"
    pure { id, sourceId, targetId, weight, properties }

-- | Network graph response
type NetworkGraphResponse =
  { nodes :: Array NetworkNode
  , edges :: Array NetworkEdge
  }

instance encodeJsonNetworkGraphResponse :: EncodeJson NetworkGraphResponse where
  encodeJson r = encodeJson
    { nodes: r.nodes
    , edges: r.edges
    }

instance decodeJsonNetworkGraphResponse :: DecodeJson NetworkGraphResponse where
  decodeJson json = do
    obj <- decodeJson json
    nodes <- obj .: "nodes"
    edges <- obj .: "edges"
    pure { nodes, edges }

-- | Post
type Post =
  { postId :: String
  , agentId :: String
  , agentUsername :: String
  , content :: String
  , contentType :: String
  , createdAt :: String
  , likesCount :: Int
  , commentsCount :: Int
  , sharesCount :: Int
  }

instance encodeJsonPost :: EncodeJson Post where
  encodeJson p = encodeJson
    { postId: p.postId
    , agentId: p.agentId
    , agentUsername: p.agentUsername
    , content: p.content
    , contentType: p.contentType
    , createdAt: p.createdAt
    , likesCount: p.likesCount
    , commentsCount: p.commentsCount
    , sharesCount: p.sharesCount
    }

instance decodeJsonPost :: DecodeJson Post where
  decodeJson json = do
    obj <- decodeJson json
    postId <- obj .: "postId"
    agentId <- obj .: "agentId"
    agentUsername <- obj .: "agentUsername"
    content <- obj .: "content"
    contentType <- obj .: "contentType"
    createdAt <- obj .: "createdAt"
    likesCount <- obj .: "likesCount"
    commentsCount <- obj .: "commentsCount"
    sharesCount <- obj .: "sharesCount"
    pure { postId, agentId, agentUsername, content, contentType, createdAt, likesCount, commentsCount, sharesCount }

-- | Feed response
type FeedResponse =
  { posts :: Array Post
  }

instance encodeJsonFeedResponse :: EncodeJson FeedResponse where
  encodeJson r = encodeJson
    { posts: r.posts
    }

instance decodeJsonFeedResponse :: DecodeJson FeedResponse where
  decodeJson json = do
    obj <- decodeJson json
    posts <- obj .: "posts"
    pure { posts }

-- | Recommendation
type Recommendation =
  { agentId :: String
  , reason :: String
  , score :: Number
  }

instance encodeJsonRecommendation :: EncodeJson Recommendation where
  encodeJson r = encodeJson
    { agentId: r.agentId
    , reason: r.reason
    , score: r.score
    }

instance decodeJsonRecommendation :: DecodeJson Recommendation where
  decodeJson json = do
    obj <- decodeJson json
    agentId <- obj .: "agentId"
    reason <- obj .: "reason"
    score <- obj .: "score"
    pure { agentId, reason, score }

-- | Discover response
type DiscoverResponse =
  { recommendations :: Array Recommendation
  }

instance encodeJsonDiscoverResponse :: EncodeJson DiscoverResponse where
  encodeJson r = encodeJson
    { recommendations: r.recommendations
    }

instance decodeJsonDiscoverResponse :: DecodeJson DiscoverResponse where
  decodeJson json = do
    obj <- decodeJson json
    recommendations <- obj .: "recommendations"
    pure { recommendations }

-- | Network metrics
type NetworkMetricsResponse =
  { totalAgents :: Int
  , totalPosts :: Int
  , totalInteractions :: Int
  , networkDensity :: Number
  , averageFollowers :: Number
  }

instance encodeJsonNetworkMetricsResponse :: EncodeJson NetworkMetricsResponse where
  encodeJson r = encodeJson
    { totalAgents: r.totalAgents
    , totalPosts: r.totalPosts
    , totalInteractions: r.totalInteractions
    , networkDensity: r.networkDensity
    , averageFollowers: r.averageFollowers
    }

instance decodeJsonNetworkMetricsResponse :: DecodeJson NetworkMetricsResponse where
  decodeJson json = do
    obj <- decodeJson json
    totalAgents <- obj .: "totalAgents"
    totalPosts <- obj .: "totalPosts"
    totalInteractions <- obj .: "totalInteractions"
    networkDensity <- obj .: "networkDensity"
    averageFollowers <- obj .: "averageFollowers"
    pure { totalAgents, totalPosts, totalInteractions, networkDensity, averageFollowers }
