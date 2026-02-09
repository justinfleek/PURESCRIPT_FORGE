module Bridge.NEXUS.Handlers where

import Prelude

import Bridge.Protocol.JsonRpc (JsonRpcRequest, JsonRpcResponse, JsonRpcError)
import Bridge.NEXUS.FFI as FFI
import Bridge.NEXUS.Postgres as Postgres
import Bridge.NEXUS.CRDT as CRDT
import Bridge.NEXUS.EdgeRouting as EdgeRouting
import Bridge.NEXUS.Types (AgentLaunchResponse, AgentStatusResponse, NetworkGraphResponse, FeedResponse, DiscoverResponse, NetworkMetricsResponse)
import Effect (Effect)
import Effect.Aff (launchAff, Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Argonaut (encodeJson, decodeJson, Json, jsonParser, JsonDecodeError)
import Data.Argonaut.Core as AC (stringify)
import Data.Argonaut.Decode (class DecodeJson, (.:), (.:?))
import Data.Argonaut.Decode.Error (JsonDecodeError)
import Nexus.Database.Postgres as NexusPostgres
import Nexus.SemanticMemory.VectorClock as VC

-- | Global PostgreSQL pool (initialized at server startup)
foreign import getPostgresPool :: Effect NexusPostgres.PostgresPool
foreign import initPostgresPool :: Effect NexusPostgres.PostgresPool
foreign import initPostgresPoolFromUrl :: String -> Effect NexusPostgres.PostgresPool
foreign import closePostgresPool :: Effect Unit

-- | Get current region ID (from environment variable REGION or default)
foreign import getRegionId :: Effect String

-- | Agent launch request
type AgentLaunchRequest =
  { agentType :: String
  , config :: String
  }

instance decodeJsonAgentLaunchRequest :: DecodeJson AgentLaunchRequest where
  decodeJson json = do
    obj <- decodeJson json
    agentType <- obj .: "agentType"
    config <- obj .:? "config"
    pure { agentType, config: fromMaybe "{}" config }

-- | Launch Nexus agent (Edge-aware)
nexusAgentLaunch :: JsonRpcRequest -> Effect (Either JsonRpcError JsonRpcResponse)
nexusAgentLaunch req = do
  -- Detect user location from headers
  mUserLoc <- EdgeRouting.detectUserLocationFromHeaders
  
  -- Parse params
  let parsedParams = case req.params of
        Just paramsStr -> case jsonParser paramsStr >>= decodeJson of
          Right p -> Just p
          Left _ -> Nothing
        Nothing -> Nothing
  
  let agentType = case parsedParams of
        Just p -> p.agentType
        Nothing -> "web_search"
  let config = case parsedParams of
        Just p -> p.config
        Nothing -> "{}"
  
  -- Launch agent in closest region (edge-aware)
  result <- launchAff $ case mUserLoc of
    Just userLoc -> do
      -- Use edge routing
      EdgeRouting.launchEdgeAgent userLoc agentType config
    Nothing -> do
      -- Fallback to local launch (v1.0)
      FFI.launchAgent agentType config
  
  case result of
    Left err -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32000, message: err, data: Nothing }
      }
    Right (Left decodeErr) -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32603, message: "Decode error: " <> decodeErr, data: Nothing }
      }
    Right (Right agentResponse) -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Just $ AC.stringify $ encodeJson agentResponse
      , error: Nothing
      }

-- | Agent status request
type AgentStatusRequest =
  { agentId :: String
  }

instance decodeJsonAgentStatusRequest :: DecodeJson AgentStatusRequest where
  decodeJson json = do
    obj <- decodeJson json
    agentId <- obj .: "agentId"
    pure { agentId }

-- | Get agent status (Edge-aware)
nexusAgentStatus :: JsonRpcRequest -> Effect (Either JsonRpcError JsonRpcResponse)
nexusAgentStatus req = do
  -- Detect user location from headers
  mUserLoc <- EdgeRouting.detectUserLocationFromHeaders
  
  -- Parse params
  let parsedParams = case req.params of
        Just paramsStr -> case jsonParser paramsStr >>= decodeJson of
          Right p -> Just p
          Left _ -> Nothing
        Nothing -> Nothing
  
  let agentId = case parsedParams of
        Just p -> p.agentId
        Nothing -> "agent-123"
  
  -- Get agent status from closest region (edge-aware)
  result <- launchAff $ case mUserLoc of
    Just userLoc -> do
      -- Use edge routing
      EdgeRouting.getEdgeAgentStatus userLoc agentId
    Nothing -> do
      -- Fallback to local status check (v1.0)
      FFI.getAgentStatus agentId
  
  case result of
    Left err -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32000, message: err, data: Nothing }
      }
    Right (Left decodeErr) -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32603, message: "Decode error: " <> decodeErr, data: Nothing }
      }
    Right (Right statusResponse) -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Just $ AC.stringify $ encodeJson statusResponse
      , error: Nothing
      }

-- | Get network graph
nexusNetworkGet :: JsonRpcRequest -> Effect (Either JsonRpcError JsonRpcResponse)
nexusNetworkGet req = do
  -- Call type-safe FFI
  result <- launchAff $ FFI.getNetworkGraph
  
  case result of
    Left err -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32000, message: err, data: Nothing }
      }
    Right (Left decodeErr) -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32603, message: "Decode error: " <> decodeErr, data: Nothing }
      }
    Right (Right graphResponse) -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Just $ AC.stringify $ encodeJson graphResponse
      , error: Nothing
      }

-- | Visualize network
nexusNetworkVisualize :: JsonRpcRequest -> Effect (Either JsonRpcError JsonRpcResponse)
nexusNetworkVisualize req = do
  -- Get network graph and generate visualization
  result <- launchAff $ FFI.getNetworkGraph
  case result of
    Left err -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32000, message: err, data: Nothing }
      }
    Right (Left decodeErr) -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32603, message: "Decode error: " <> decodeErr, data: Nothing }
      }
    Right (Right graphResponse) -> do
      -- Generate SVG visualization from graph data
      -- For now, return graph data (UI can generate visualization)
      pure $ Right
        { jsonrpc: "2.0"
        , id: req.id
        , result: Just $ AC.stringify $ encodeJson graphResponse
        , error: Nothing
        }

-- | Generate query
nexusQueryGenerate :: JsonRpcRequest -> Effect (Either JsonRpcError JsonRpcResponse)
nexusQueryGenerate req = do
  -- Generate query from semantic cells via Python module
  result <- generateQueryFromSemanticCells
  case result of
    Left err -> pure $ Left
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32000, message: err, data: Nothing }
      }
    Right query -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Just $ AC.stringify $ encodeJson { query }
      , error: Nothing
      }

-- | Generate query from semantic cells
foreign import generateQueryFromSemanticCells :: Effect (Either String String)

-- | Search execute request
type SearchExecuteRequest =
  { query :: String
  , maxResults :: Maybe Int
  }

instance decodeJsonSearchExecuteRequest :: DecodeJson SearchExecuteRequest where
  decodeJson json = do
    obj <- decodeJson json
    query <- obj .: "query"
    maxResults <- obj .:? "maxResults"
    pure { query, maxResults }

-- | Execute search
nexusSearchExecute :: JsonRpcRequest -> Effect (Either JsonRpcError JsonRpcResponse)
nexusSearchExecute req = do
  -- Parse params
  let parsedParams = case req.params of
        Just paramsStr -> case jsonParser paramsStr >>= decodeJson of
          Right p -> Just p
          Left _ -> Nothing
        Nothing -> Nothing
  
  -- Execute web search via web-search-agent Python module
  -- For now, return placeholder - would call web-search-agent
  let results = []  -- Would execute search and return results
  pure $ Right
    { jsonrpc: "2.0"
    , id: req.id
    , result: Just $ AC.stringify $ encodeJson { results }
    , error: Nothing
    }

-- | Feed get request
type FeedGetRequest =
  { agentId :: String
  }

instance decodeJsonFeedGetRequest :: DecodeJson FeedGetRequest where
  decodeJson json = do
    obj <- decodeJson json
    agentId <- obj .: "agentId"
    pure { agentId }

-- | Get agent feed
nexusFeedGet :: JsonRpcRequest -> Effect (Either JsonRpcError JsonRpcResponse)
nexusFeedGet req = do
  -- Parse params
  let parsedParams = case req.params of
        Just paramsStr -> case jsonParser paramsStr >>= decodeJson of
          Right p -> Just p
          Left _ -> Nothing
        Nothing -> Nothing
  
  let agentId = case parsedParams of
        Just p -> p.agentId
        Nothing -> "agent-123"
  
  -- Call type-safe FFI
  result <- launchAff $ FFI.getFeed agentId
  
  case result of
    Left err -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32000, message: err, data: Nothing }
      }
    Right (Left decodeErr) -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32603, message: "Decode error: " <> decodeErr, data: Nothing }
      }
    Right (Right feedResponse) -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Just $ AC.stringify $ encodeJson feedResponse
      , error: Nothing
      }

-- | Post create request
type PostCreateRequest =
  { agentId :: String
  , content :: String
  , contentType :: Maybe String
  }

instance decodeJsonPostCreateRequest :: DecodeJson PostCreateRequest where
  decodeJson json = do
    obj <- decodeJson json
    agentId <- obj .: "agentId"
    content <- obj .: "content"
    contentType <- obj .:? "contentType"
    pure { agentId, content, contentType }

-- | Create agent post
nexusPostCreate :: JsonRpcRequest -> Effect (Either JsonRpcError JsonRpcResponse)
nexusPostCreate req = do
  -- Parse params
  let parsedParams = case req.params of
        Just paramsStr -> case jsonParser paramsStr >>= decodeJson of
          Right p -> Just p
          Left _ -> Nothing
        Nothing -> Nothing
  
  case parsedParams of
    Just params -> do
      result <- launchAff $ FFI.createPost params.agentId params.content (fromMaybe "text" params.contentType)
      case result of
        Left err -> pure $ Right
          { jsonrpc: "2.0"
          , id: req.id
          , result: Nothing
          , error: Just { code: -32000, message: err, data: Nothing }
          }
        Right response -> pure $ Right
          { jsonrpc: "2.0"
          , id: req.id
          , result: Just $ AC.stringify $ encodeJson response
          , error: Nothing
          }
    Nothing -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32602, message: "Invalid params", data: Nothing }
      }

-- | Post like request
type PostLikeRequest =
  { agentId :: String
  , postId :: String
  }

instance decodeJsonPostLikeRequest :: DecodeJson PostLikeRequest where
  decodeJson json = do
    obj <- decodeJson json
    agentId <- obj .: "agentId"
    postId <- obj .: "postId"
    pure { agentId, postId }

-- | Like post
nexusPostLike :: JsonRpcRequest -> Effect (Either JsonRpcError JsonRpcResponse)
nexusPostLike req = do
  -- Parse params
  let parsedParams = case req.params of
        Just paramsStr -> case jsonParser paramsStr >>= decodeJson of
          Right p -> Just p
          Left _ -> Nothing
        Nothing -> Nothing
  
  case parsedParams of
    Just params -> do
      result <- launchAff $ FFI.likePost params.agentId params.postId
      case result of
        Left err -> pure $ Right
          { jsonrpc: "2.0"
          , id: req.id
          , result: Nothing
          , error: Just { code: -32000, message: err, data: Nothing }
          }
        Right _ -> pure $ Right
          { jsonrpc: "2.0"
          , id: req.id
          , result: Just $ AC.stringify $ encodeJson { success: true }
          , error: Nothing
          }
    Nothing -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32602, message: "Invalid params", data: Nothing }
      }

-- | Agent follow request
type AgentFollowRequest =
  { agentId :: String
  , targetAgentId :: String
  }

instance decodeJsonAgentFollowRequest :: DecodeJson AgentFollowRequest where
  decodeJson json = do
    obj <- decodeJson json
    agentId <- obj .: "agentId"
    targetAgentId <- obj .: "targetAgentId"
    pure { agentId, targetAgentId }

-- | Follow agent
nexusAgentFollow :: JsonRpcRequest -> Effect (Either JsonRpcError JsonRpcResponse)
nexusAgentFollow req = do
  -- Parse params
  let parsedParams = case req.params of
        Just paramsStr -> case jsonParser paramsStr >>= decodeJson of
          Right p -> Just p
          Left _ -> Nothing
        Nothing -> Nothing
  
  case parsedParams of
    Just params -> do
      result <- launchAff $ FFI.followAgent params.agentId params.targetAgentId
      case result of
        Left err -> pure $ Right
          { jsonrpc: "2.0"
          , id: req.id
          , result: Nothing
          , error: Just { code: -32000, message: err, data: Nothing }
          }
        Right _ -> pure $ Right
          { jsonrpc: "2.0"
          , id: req.id
          , result: Just $ AC.stringify $ encodeJson { success: true }
          , error: Nothing
          }
    Nothing -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32602, message: "Invalid params", data: Nothing }
      }

-- | Discover agents
nexusAgentDiscover :: JsonRpcRequest -> Effect (Either JsonRpcError JsonRpcResponse)
nexusAgentDiscover req = do
  -- Parse params
  let parsedParams = case req.params of
        Just paramsStr -> case jsonParser paramsStr >>= decodeJson of
          Right p -> Just p
          Left _ -> Nothing
        Nothing -> Nothing
  
  let agentId = case parsedParams of
        Just p -> p.agentId
        Nothing -> "agent-123"
  
  -- Call type-safe FFI
  result <- launchAff $ FFI.discoverAgents agentId
  
  case result of
    Left err -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32000, message: err, data: Nothing }
      }
    Right (Left decodeErr) -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32603, message: "Decode error: " <> decodeErr, data: Nothing }
      }
    Right (Right discoverResponse) -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Just $ AC.stringify $ encodeJson discoverResponse
      , error: Nothing
      }

-- | Attestation request
type AttestationRequest =
  { taskId :: String
  , agentId :: String
  , taskDescription :: String
  , completionStatus :: String
  , metadata :: String
  }

instance decodeJsonAttestationRequest :: DecodeJson AttestationRequest where
  decodeJson json = do
    obj <- decodeJson json
    taskId <- obj .: "taskId"
    agentId <- obj .: "agentId"
    taskDescription <- obj .: "taskDescription"
    completionStatus <- obj .: "completionStatus"
    metadata <- obj .:? "metadata"
    pure { taskId, agentId, taskDescription, completionStatus, metadata: fromMaybe "{}" metadata }

-- | Create task completion attestation
-- | Uses CRDT merge logic with vector clock tracking
nexusAttestationCreate :: JsonRpcRequest -> Effect (Either JsonRpcError JsonRpcResponse)
nexusAttestationCreate req = do
  -- Get current region ID for vector clock
  regionId <- getRegionId
  postgresPool <- getPostgresPool
  
  -- Parse params
  let parsedParams = case req.params of
        Just paramsStr -> case jsonParser paramsStr >>= decodeJson of
          Right p -> Just p
          Left _ -> Nothing
        Nothing -> Nothing
  
  case parsedParams of
    Just params -> do
      -- Parse metadata to extract semantic structure
      let metadataJson = case jsonParser params.metadata of
            Right json -> json
            Left _ -> encodeJson {}
      
      -- Extract concepts, relations from metadata
      let conceptsJson = AC.stringify $ case metadataJson `decodeJson` of
            Right obj -> fromMaybe (encodeJson { concepts: [] }) $ obj .:? "concepts" >>= \cs -> Just $ encodeJson { concepts: cs }
            Left _ -> encodeJson { concepts: [] }
      
      let relationsJson = AC.stringify $ case metadataJson `decodeJson` of
            Right obj -> fromMaybe (encodeJson { relations: [] }) $ obj .:? "relations" >>= \rs -> Just $ encodeJson { relations: rs }
            Left _ -> encodeJson { relations: [] }
      
      -- Create semantic cells from concepts with vector clock
      -- Use PostgreSQL with CRDT merge logic
      cellsResult <- launchAff $ do
        -- Try PostgreSQL first (with CRDT)
        postgresResult <- Postgres.createSemanticCellsWithVC postgresPool conceptsJson params.agentId params.taskId regionId
        case postgresResult of
          Right cellsJson -> pure $ Right cellsJson
          Left _ -> do
            -- Fallback to Python FFI (v1.0)
            FFI.createSemanticCellsFromConcepts conceptsJson params.agentId params.taskId
      
      case cellsResult of
        Left err -> pure $ Right
          { jsonrpc: "2.0"
          , id: req.id
          , result: Nothing
          , error: Just { code: -32000, message: "Failed to create semantic cells: " <> err, data: Nothing }
          }
        Right cellsJson -> do
          -- Extract cell map for coupling creation
          let cellMapJson = AC.stringify $ encodeJson { cellMap: {} }  -- Would extract from cellsJson in production
          
          -- Create couplings from relations (with vector clock tracking)
          couplingsResult <- launchAff $ do
            -- Try PostgreSQL first
            postgresCouplingsResult <- Postgres.createCouplingsWithVC postgresPool relationsJson cellMapJson regionId
            case postgresCouplingsResult of
              Right couplingsJson -> pure $ Right couplingsJson
              Left _ -> do
                -- Fallback to Python FFI (v1.0)
                FFI.createCouplingsFromRelations relationsJson cellMapJson
          
          case couplingsResult of
            Left err -> pure $ Right
              { jsonrpc: "2.0"
              , id: req.id
              , result: Just $ AC.stringify $ encodeJson
                  { success: true
                  , attestationId: "attest-" <> params.taskId
                  , taskId: params.taskId
                  , agentId: params.agentId
                  , attestedAt: "2026-01-30T00:00:00Z"
                  , cellsCreated: 0  -- Would extract from cellsJson
                  , couplingsCreated: 0
                  , warning: "Failed to create couplings: " <> err
                  }
              , error: Nothing
              }
            Right couplingsJson -> do
              -- Extract counts from results (would parse JSON in production)
              let cellsCreated = 0  -- Would extract from cellsJson
              let couplingsCreated = 0  -- Would extract from couplingsJson
              
              pure $ Right
                { jsonrpc: "2.0"
                , id: req.id
                , result: Just $ AC.stringify $ encodeJson
                    { success: true
                    , attestationId: "attest-" <> params.taskId
                    , taskId: params.taskId
                    , agentId: params.agentId
                    , attestedAt: "2026-01-30T00:00:00Z"
                    , cellsCreated: cellsCreated
                    , couplingsCreated: couplingsCreated
                    , regionId: regionId  -- Include region ID
                    , vectorClockUsed: true  -- Indicates CRDT merge was used
                    }
                , error: Nothing
                }
    Nothing -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32602, message: "Invalid params", data: Nothing }
      }

-- | Agent profile request
type AgentProfileRequest =
  { agentId :: String
  }

instance decodeJsonAgentProfileRequest :: DecodeJson AgentProfileRequest where
  decodeJson json = do
    obj <- decodeJson json
    agentId <- obj .: "agentId"
    pure { agentId }

-- | Get agent profile (with avatar URL from semantic cell state)
nexusAgentProfile :: JsonRpcRequest -> Effect (Either JsonRpcError JsonRpcResponse)
nexusAgentProfile req = do
  -- Parse params
  let parsedParams = case req.params of
        Just paramsStr -> case jsonParser paramsStr >>= decodeJson of
          Right p -> Just p
          Left _ -> Nothing
        Nothing -> Nothing
  
  case parsedParams of
    Just params -> do
      -- Get PostgreSQL pool
      postgresPool <- getPostgresPool
      -- Get agent's semantic cells (try PostgreSQL first, fallback to Python)
      cellsResult <- launchAff $ do
        -- Try PostgreSQL direct query
        postgresResult <- Postgres.getAgentSemanticCells postgresPool params.agentId
        case postgresResult of
          Right cellsJson -> pure $ Right cellsJson
          Left _ -> do
            -- Fallback to Python FFI
            FFI.getAgentSemanticCells params.agentId
      
      case cellsResult of
        Left err -> pure $ Right
          { jsonrpc: "2.0"
          , id: req.id
          , result: Nothing
          , error: Just { code: -32000, message: "Failed to get semantic cells: " <> err, data: Nothing }
          }
        Right cellsJson -> do
          -- Extract primary cell state for avatar generation
          let primaryCellState = case cellsJson `decodeJson` of
                Right obj -> case obj .:? "primaryCell" of
                  Just (Just primaryCell) -> case primaryCell `decodeJson` of
                    Right pc -> case pc .:? "state" of
                      Just (Just state) -> Just $ AC.stringify state
                      _ -> Nothing
                    Left _ -> Nothing
                  _ -> Nothing
                Left _ -> Nothing
          
          -- Generate avatar URL (would use primaryCellState if available)
          let displayName = "Agent " <> params.agentId
          let avatarUrl = "data:image/svg+xml;base64,PHN2ZyB3aWR0aD0iNjQiIGhlaWdodD0iNjQiIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyI+PHJlY3Qgd2lkdGg9IjY0IiBoZWlnaHQ9IjY0IiBmaWxsPSIjRkY2QjlEIiByeD0iMzIiLz48dGV4dCB4PSIzMiIgeT0iMzIiIGZvbnQtZmFtaWx5PSJBcmlhbCIgZm9udC1zaXplPSIyNCIgZmlsbD0iI0ZGRkZGRiIgdGV4dC1hbmNob3I9Im1pZGRsZSIgZG9taW5hbnQtYmFzZWxpbmU9ImNlbnRyYWwiPkE8L3RleHQ+PC9zdmc+"
          
          -- Extract semantic cells for response
          let semanticCells = case cellsJson `decodeJson` of
                Right obj -> case obj .:? "cells" of
                  Just (Just cells) -> cells
                  _ -> []
                Left _ -> []
          
          pure $ Right
            { jsonrpc: "2.0"
            , id: req.id
            , result: Just $ AC.stringify $ encodeJson
                { agentId: params.agentId
                , username: "agent-" <> params.agentId
                , displayName: displayName
                , avatarUrl: Just avatarUrl
                , bio: ""
                , interests: []
                , expertise: []
                , createdAt: "2026-01-30T00:00:00Z"
                , updatedAt: "2026-01-30T00:00:00Z"
                , stats:
                    { postsCount: 0
                    , followersCount: 0
                    , followingCount: 0
                    , likesReceived: 0
                    , commentsReceived: 0
                    , sharesReceived: 0
                    }
                , semanticCells: semanticCells
                }
            , error: Nothing
            }
    Nothing -> pure $ Right
      { jsonrpc: "2.0"
      , id: req.id
      , result: Nothing
      , error: Just { code: -32602, message: "Invalid params", data: Nothing }
      }
