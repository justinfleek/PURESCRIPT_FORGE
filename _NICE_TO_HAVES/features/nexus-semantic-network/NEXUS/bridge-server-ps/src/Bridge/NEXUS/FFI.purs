module Bridge.NEXUS.FFI where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff, makeAff, nonCanceler)
import Data.Either (Either(..))
import Data.Argonaut (Json, decodeJson, class DecodeJson)
import Data.Argonaut.Core as AC (jsonParser)
import Data.Maybe (Maybe(..))
import Bridge.NEXUS.Types
  ( AgentLaunchResponse
  , AgentStatusResponse
  , NetworkGraphResponse
  , FeedResponse
  , DiscoverResponse
  , NetworkMetricsResponse
  )

-- | FFI functions for Python NEXUS integration
-- | These return JSON strings that we decode safely
foreign import launchAgent_ :: String -> String -> Effect String
foreign import getAgentStatus_ :: String -> Effect String
foreign import getNetworkGraph_ :: Effect String
foreign import createPost_ :: String -> String -> String -> Effect String
foreign import likePost_ :: String -> String -> Effect String
foreign import followAgent_ :: String -> String -> Effect String
foreign import getFeed_ :: String -> Effect String
foreign import discoverAgents_ :: String -> Effect String
foreign import sendMessage_ :: String -> String -> String -> Effect String
foreign import getConversations_ :: String -> Effect String
foreign import getNetworkMetrics_ :: Effect String
foreign import getAgentMetrics_ :: String -> Effect String
foreign import createSemanticCellsFromConcepts_ :: String -> String -> String -> Effect String
foreign import createCouplingsFromRelations_ :: String -> String -> Effect String
foreign import getAgentSemanticCells_ :: String -> Effect String

-- | Safe JSON decode helper
decodeJsonString :: forall a. DecodeJson a => String -> Either String a
decodeJsonString str = do
  json <- AC.jsonParser str
  decodeJson json

-- | Launch NEXUS agent
launchAgent :: String -> String -> Aff (Either String AgentLaunchResponse)
launchAgent agentType config = makeAff \callback -> do
  resultStr <- launchAgent_ agentType config
  case decodeJsonString resultStr of
    Left err -> callback $ Left $ "Decode error: " <> err
    Right result -> callback $ Right result
  pure nonCanceler

-- | Get agent status
getAgentStatus :: String -> Aff (Either String AgentStatusResponse)
getAgentStatus agentId = makeAff \callback -> do
  resultStr <- getAgentStatus_ agentId
  case decodeJsonString resultStr of
    Left err -> callback $ Left $ "Decode error: " <> err
    Right result -> callback $ Right result
  pure nonCanceler

-- | Get network graph
getNetworkGraph :: Aff (Either String NetworkGraphResponse)
getNetworkGraph = makeAff \callback -> do
  resultStr <- getNetworkGraph_ unit
  case decodeJsonString resultStr of
    Left err -> callback $ Left $ "Decode error: " <> err
    Right result -> callback $ Right result
  pure nonCanceler

-- | Create agent post
createPost :: String -> String -> String -> Aff (Either String { postId :: String, success :: Boolean })
createPost agentId content contentType = makeAff \callback -> do
  resultStr <- createPost_ agentId content contentType
  case decodeJsonString resultStr of
    Left err -> callback $ Left $ "Decode error: " <> err
    Right result -> callback $ Right result
  pure nonCanceler

-- | Like post
likePost :: String -> String -> Aff (Either String Unit)
likePost agentId postId = makeAff \callback -> do
  _ <- likePost_ agentId postId
  callback $ Right unit
  pure nonCanceler

-- | Follow agent
followAgent :: String -> String -> Aff (Either String Unit)
followAgent agentId targetAgentId = makeAff \callback -> do
  _ <- followAgent_ agentId targetAgentId
  callback $ Right unit
  pure nonCanceler

-- | Get agent feed
getFeed :: String -> Aff (Either String FeedResponse)
getFeed agentId = makeAff \callback -> do
  resultStr <- getFeed_ agentId
  case decodeJsonString resultStr of
    Left err -> callback $ Left $ "Decode error: " <> err
    Right result -> callback $ Right result
  pure nonCanceler

-- | Discover agents
discoverAgents :: String -> Aff (Either String DiscoverResponse)
discoverAgents agentId = makeAff \callback -> do
  resultStr <- discoverAgents_ agentId
  case decodeJsonString resultStr of
    Left err -> callback $ Left $ "Decode error: " <> err
    Right result -> callback $ Right result
  pure nonCanceler

-- | Send message
sendMessage :: String -> String -> String -> Aff (Either String { messageId :: String, success :: Boolean })
sendMessage senderId recipientId content = makeAff \callback -> do
  resultStr <- sendMessage_ senderId recipientId content
  case decodeJsonString resultStr of
    Left err -> callback $ Left $ "Decode error: " <> err
    Right result -> callback $ Right result
  pure nonCanceler

-- | Get conversations
getConversations :: String -> Aff (Either String Json)
getConversations agentId = makeAff \callback -> do
  resultStr <- getConversations_ agentId
  case AC.jsonParser resultStr of
    Left err -> callback $ Left $ "Parse error: " <> err
    Right json -> callback $ Right json
  pure nonCanceler

-- | Get network metrics
getNetworkMetrics :: Aff (Either String NetworkMetricsResponse)
getNetworkMetrics = makeAff \callback -> do
  resultStr <- getNetworkMetrics_ unit
  case decodeJsonString resultStr of
    Left err -> callback $ Left $ "Decode error: " <> err
    Right result -> callback $ Right result
  pure nonCanceler

-- | Get agent metrics
getAgentMetrics :: String -> Aff (Either String Json)
getAgentMetrics agentId = makeAff \callback -> do
  resultStr <- getAgentMetrics_ agentId
  case AC.jsonParser resultStr of
    Left err -> callback $ Left $ "Parse error: " <> err
    Right json -> callback $ Right json
  pure nonCanceler

-- | Create semantic cells from concepts
createSemanticCellsFromConcepts :: String -> String -> String -> Aff (Either String Json)
createSemanticCellsFromConcepts conceptsJson agentId taskId = makeAff \callback -> do
  resultStr <- createSemanticCellsFromConcepts_ conceptsJson agentId taskId
  case AC.jsonParser resultStr of
    Left err -> callback $ Left $ "Parse error: " <> err
    Right json -> callback $ Right json
  pure nonCanceler

-- | Create couplings from relations
createCouplingsFromRelations :: String -> String -> Aff (Either String Json)
createCouplingsFromRelations relationsJson cellMapJson = makeAff \callback -> do
  resultStr <- createCouplingsFromRelations_ relationsJson cellMapJson
  case AC.jsonParser resultStr of
    Left err -> callback $ Left $ "Parse error: " <> err
    Right json -> callback $ Right json
  pure nonCanceler

-- | Get agent semantic cells
getAgentSemanticCells :: String -> Aff (Either String Json)
getAgentSemanticCells agentId = makeAff \callback -> do
  resultStr <- getAgentSemanticCells_ agentId
  case AC.jsonParser resultStr of
    Left err -> callback $ Left $ "Parse error: " <> err
    Right json -> callback $ Right json
  pure nonCanceler
