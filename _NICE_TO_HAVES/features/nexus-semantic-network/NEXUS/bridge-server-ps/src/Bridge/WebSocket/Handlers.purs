-- | WebSocket JSON-RPC Handlers - NEXUS Handler Registration
module Bridge.WebSocket.Handlers where

import Prelude
import Effect (Effect)
import Effect.Ref (read)
import Data.Argonaut (jsonParser, decodeJson, encodeJson, class EncodeJson)
import Data.Argonaut.Core as AC (stringify)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Map as Map
import Bridge.Protocol.JsonRpc (JsonRpcRequest, JsonRpcResponse, JsonRpcError)
import Bridge.NEXUS.Handlers as NEXUS
import Bridge.WebSocket.Manager (WebSocketManager, registerHandler)

-- | Register all NEXUS handlers
registerNexusHandlers :: WebSocketManager -> Effect Unit
registerNexusHandlers manager = do
  -- Helper to wrap handler
  let wrapHandler handler = \paramsStr -> do
        case jsonParser paramsStr >>= decodeJson of
          Left _ -> pure $ AC.stringify $ encodeJson
            { jsonrpc: "2.0"
            , id: Nothing
            , result: Nothing
            , error: Just { code: -32602, message: "Invalid params", data: Nothing }
            }
          Right req -> do
            result <- handler req
            case result of
              Left err -> pure $ AC.stringify $ encodeJson
                { jsonrpc: "2.0"
                , id: req.id
                , result: Nothing
                , error: Just err
                }
              Right resp -> pure $ AC.stringify $ encodeJson resp
  
  -- Register all NEXUS handlers
  registerHandler manager "nexus.agent.launch" (wrapHandler NEXUS.nexusAgentLaunch)
  registerHandler manager "nexus.agent.status" (wrapHandler NEXUS.nexusAgentStatus)
  registerHandler manager "nexus.network.get" (wrapHandler NEXUS.nexusNetworkGet)
  registerHandler manager "nexus.network.visualize" (wrapHandler NEXUS.nexusNetworkVisualize)
  registerHandler manager "nexus.query.generate" (wrapHandler NEXUS.nexusQueryGenerate)
  registerHandler manager "nexus.search.execute" (wrapHandler NEXUS.nexusSearchExecute)
  registerHandler manager "nexus.feed.get" (wrapHandler NEXUS.nexusFeedGet)
  registerHandler manager "nexus.post.create" (wrapHandler NEXUS.nexusPostCreate)
  registerHandler manager "nexus.post.like" (wrapHandler NEXUS.nexusPostLike)
  registerHandler manager "nexus.agent.follow" (wrapHandler NEXUS.nexusAgentFollow)
  registerHandler manager "nexus.agent.discover" (wrapHandler NEXUS.nexusAgentDiscover)
  registerHandler manager "nexus.attestation.create" (wrapHandler NEXUS.nexusAttestationCreate)
  registerHandler manager "nexus.agent.profile" (wrapHandler NEXUS.nexusAgentProfile)

-- | Handle JSON-RPC message and route to handler
handleJsonRpcMessage :: WebSocketManager -> String -> Effect String
handleJsonRpcMessage manager message = do
  case jsonParser message >>= decodeJson of
    Left _ -> pure $ AC.stringify $ encodeJson
      { jsonrpc: "2.0"
      , id: Nothing
      , result: Nothing
      , error: Just { code: -32700, message: "Parse error", data: Nothing }
      }
    Right req -> do
      handlerMap <- read manager.handlerMap
      case Map.lookup req.method handlerMap of
        Just handler -> handler (fromMaybe "{}" req.params)
        Nothing -> pure $ AC.stringify $ encodeJson
          { jsonrpc: "2.0"
          , id: req.id
          , result: Nothing
          , error: Just { code: -32601, message: "Method not found: " <> req.method, data: Nothing }
          }
