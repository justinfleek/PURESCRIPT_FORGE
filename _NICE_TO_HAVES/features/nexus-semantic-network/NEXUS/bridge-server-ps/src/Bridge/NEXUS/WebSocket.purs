module Bridge.NEXUS.WebSocket where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Foreign (Foreign)
import Data.Argonaut (encodeJson, decodeJson, Json, jsonParser, class EncodeJson, class DecodeJson, (.:), (.:?))
import Data.Argonaut.Core as AC (stringify)
import Bridge.Protocol.JsonRpc (JsonRpcRequest, JsonRpcResponse)

-- | WebSocket notifications for NEXUS
data NEXUSNotification
  = NewPost { agentId :: String, postId :: String, content :: String }
  | NewLike { agentId :: String, postId :: String }
  | NewComment { agentId :: String, postId :: String, comment :: String }
  | NewFollow { agentId :: String, targetAgentId :: String }
  | NewMessage { senderId :: String, recipientId :: String, content :: String }
  | NetworkUpdate { nodes :: Array Foreign, edges :: Array Foreign }
  | AgentStatusChange { agentId :: String, status :: String }

derive instance eqNEXUSNotification :: Eq NEXUSNotification

instance encodeJsonNEXUSNotification :: EncodeJson NEXUSNotification where
  encodeJson = case _ of
    NewPost r -> encodeJson { type: "new_post", agentId: r.agentId, postId: r.postId, content: r.content }
    NewLike r -> encodeJson { type: "new_like", agentId: r.agentId, postId: r.postId }
    NewComment r -> encodeJson { type: "new_comment", agentId: r.agentId, postId: r.postId, comment: r.comment }
    NewFollow r -> encodeJson { type: "new_follow", agentId: r.agentId, targetAgentId: r.targetAgentId }
    NewMessage r -> encodeJson { type: "new_message", senderId: r.senderId, recipientId: r.recipientId, content: r.content }
    NetworkUpdate r -> encodeJson { type: "network_update", nodes: r.nodes, edges: r.edges }
    AgentStatusChange r -> encodeJson { type: "agent_status_change", agentId: r.agentId, status: r.status }

instance decodeJsonNEXUSNotification :: DecodeJson NEXUSNotification where
  decodeJson json = do
    obj <- decodeJson json
    type_ <- obj .: "type"
    case type_ of
      "new_post" -> do
        agentId <- obj .: "agentId"
        postId <- obj .: "postId"
        content <- obj .: "content"
        pure $ NewPost { agentId, postId, content }
      "new_like" -> do
        agentId <- obj .: "agentId"
        postId <- obj .: "postId"
        pure $ NewLike { agentId, postId }
      "new_comment" -> do
        agentId <- obj .: "agentId"
        postId <- obj .: "postId"
        comment <- obj .: "comment"
        pure $ NewComment { agentId, postId, comment }
      "new_follow" -> do
        agentId <- obj .: "agentId"
        targetAgentId <- obj .: "targetAgentId"
        pure $ NewFollow { agentId, targetAgentId }
      "new_message" -> do
        senderId <- obj .: "senderId"
        recipientId <- obj .: "recipientId"
        content <- obj .: "content"
        pure $ NewMessage { senderId, recipientId, content }
      "network_update" -> do
        nodes <- obj .: "nodes"
        edges <- obj .: "edges"
        pure $ NetworkUpdate { nodes, edges }
      "agent_status_change" -> do
        agentId <- obj .: "agentId"
        status <- obj .: "status"
        pure $ AgentStatusChange { agentId, status }
      _ -> Left "Unknown notification type"

-- | Set global WebSocket manager (called by Bridge.Server)
foreign import setGlobalWebSocketManager :: Foreign -> Effect Unit

-- | Subscribe to NEXUS notifications
foreign import subscribeNEXUS_ :: (Foreign -> Effect Unit) -> Effect Unit

-- | Unsubscribe from NEXUS notifications
foreign import unsubscribeNEXUS_ :: Effect Unit

-- | Convert Foreign to JSON string
foreign import foreignToJsonString :: Foreign -> Effect String

-- | Convert JSON string to Foreign
foreign import jsonStringToForeign :: String -> Effect Foreign

-- | Subscribe to NEXUS notifications
subscribeNEXUS :: (NEXUSNotification -> Effect Unit) -> Effect Unit
subscribeNEXUS handler = subscribeNEXUS_ \foreignNotification -> do
  -- Parse notification from Foreign
  -- Convert Foreign to JSON string, then decode
  notificationJsonStr <- foreignToJsonString foreignNotification
  case jsonParser notificationJsonStr >>= decodeJson of
    Left _ -> pure unit  -- Ignore parse errors
    Right notification -> handler notification

-- | Broadcast NEXUS notification
foreign import broadcastNEXUS_ :: String -> Foreign -> Effect Unit

-- | Broadcast NEXUS notification
broadcastNEXUS :: NEXUSNotification -> Effect Unit
broadcastNEXUS notification = do
  -- Serialize notification to JSON
  let json = encodeJson notification
  let jsonStr = AC.stringify json
  -- Convert JSON string to Foreign
  foreignJson <- jsonStringToForeign jsonStr
  broadcastNEXUS_ jsonStr foreignJson
