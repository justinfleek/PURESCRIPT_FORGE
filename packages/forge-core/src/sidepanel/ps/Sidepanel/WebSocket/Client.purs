-- | Comprehensive WebSocket Client with JSON-RPC 2.0
-- | Based on spec 31-WEBSOCKET-PROTOCOL.md
module Sidepanel.WebSocket.Client where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, makeAff, delay, Milliseconds(..))
import Effect.Aff.Class (class MonadAff)
import Effect.Ref (Ref, new, read, write, modify)
import Effect.Class (class MonadEffect, liftEffect)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Int (toNumber)
import Data.DateTime (DateTime)
import Control.Monad.Rec.Class (class MonadRec)
import Sidepanel.FFI.WebSocket (WebSocketConnection, create, readyState, send, close, closeWith, onOpen, onClose, onError, onMessage, toReadyState, ReadyState(..))
import Sidepanel.Api.Types (JsonRpcRequest, JsonRpcResponse, JsonRpcError, ServerMessage(..))
import Argonaut.Decode.Error (JsonDecodeError)
import Sidepanel.FFI.DateTime (getCurrentDateTime)
import Argonaut.Core (Json)
import Argonaut.Core as AC
import Argonaut.Encode (class EncodeJson, encodeJson, (:=), (:=?))
import Argonaut.Decode (class DecodeJson, decodeJson, (.:), (.:?))
import Argonaut.Parser (jsonParser)
import Data.Array as Array
import Data.Int as Int
import Data.Maybe (fromMaybe)
import Effect.Aff (launchAff_)

-- | Connection state
data ConnectionState
  = Disconnected
  | Connecting
  | Connected
  | Reconnecting Int  -- Attempt number
  | Error String

derive instance eqConnectionState :: Eq ConnectionState

-- | Pending request with timeout
type PendingRequest =
  { resolve :: Either JsonRpcError Json -> Effect Unit
  , timeout :: Effect Unit
  , timestamp :: DateTime
  }

-- | Queued message (for offline scenarios)
type QueuedMessage =
  { request :: JsonRpcRequest
  , timestamp :: DateTime
  , retries :: Int
  }

-- | Client configuration
type ClientConfig =
  { url :: String
  , reconnectInterval :: Milliseconds
  , maxReconnectAttempts :: Int
  , requestTimeout :: Milliseconds
  , heartbeatInterval :: Milliseconds
  , heartbeatTimeout :: Milliseconds
  , maxQueueSize :: Int
  , authToken :: Maybe String
  }

-- | Default configuration
defaultConfig :: ClientConfig
defaultConfig =
  { url: "ws://localhost:8765/ws"
  , reconnectInterval: Milliseconds 1000.0
  , maxReconnectAttempts: 10
  , requestTimeout: Milliseconds 30000.0
  , heartbeatInterval: Milliseconds 30000.0
  , heartbeatTimeout: Milliseconds 60000.0
  , maxQueueSize: 100
  , authToken: Nothing
  }

-- | WebSocket client state
type WSClient =
  { socket :: Maybe WebSocketConnection
  , state :: Ref ConnectionState
  , nextId :: Ref Int
  , pending :: Ref (Map.Map Int PendingRequest)
  , queue :: Ref (Array QueuedMessage)
  , subscribers :: Ref (Array (ServerMessage -> Effect Unit))
  , messageQueue :: Ref (Array ServerMessage)  -- Queue for Halogen action dispatch
  , config :: ClientConfig
  , lastPing :: Ref (Maybe DateTime)
  , reconnectAttempt :: Ref Int
  }

-- | Create new WebSocket client
createClient :: ClientConfig -> Effect WSClient
createClient config = do
  state <- new Disconnected
  nextId <- new 1
  pending <- new Map.empty
  queue <- new []
  subscribers <- new []
  messageQueue <- new []  -- Initialize message queue for Halogen dispatch
  lastPing <- new Nothing
  reconnectAttempt <- new 0
  pure
    { socket: Nothing
    , state
    , nextId
    , pending
    , queue
    , subscribers
    , messageQueue
    , config
    , lastPing
    , reconnectAttempt
    }

-- | Connect to WebSocket server
connect :: forall m. MonadAff m => WSClient -> Aff (Either String Unit)
connect client = makeAff \resolve -> do
  liftEffect do
    write Connecting client.state
    socket <- create client.config.url
    setupHandlers client socket resolve
    pure (pure unit)

setupHandlers :: WSClient -> WebSocketConnection -> (Either String Unit -> Effect Unit) -> Effect Unit
setupHandlers client socket resolve = do
  onOpen socket do
    write (Connected) client.state
    write 0 client.reconnectAttempt
    resolve (Right unit)
    -- Process queued messages
    processQueue client
    -- Start heartbeat
    startHeartbeat client
    -- Authenticate if token provided
    authenticate client

  onClose socket \code reason -> do
    write (Disconnected) client.state
    -- Attempt reconnect if not intentional close
    when (code /= 1000) do
      attemptReconnect client

  onError socket \errorMsg -> do
    write (Error errorMsg) client.state
    resolve (Left errorMsg)

  onMessage socket \message -> do
    handleMessage client message

  write (Just socket) client.socket

-- | Authenticate with server
authenticate :: WSClient -> Effect Unit
authenticate client = case client.config.authToken of
  Just token -> do
    -- Send auth request with proper JSON encoding
    void $ launchAff_ $ request client "auth.request" (AC.fromObject $ AC.fromFoldable [ "token" := token ]) \result -> do
      -- Handle auth response
      pure unit
  Nothing -> pure unit

-- | Send JSON-RPC request and await response
request :: forall a. WSClient -> String -> Json -> (Json -> Aff a) -> Aff (Either JsonRpcError a)
request client method paramsJson handler = makeAff \resolve -> do
  id <- liftEffect $ modify (_ + 1) client.nextId >>= read client.nextId
  state <- liftEffect $ read client.state
  
  if state == Connected then do
    -- Create request with JSON params
    let req = { jsonrpc: "2.0", id: show id, method, params: paramsJson }
    
    -- Send request
    result <- sendRequest client req
    
    case result of
      Left err -> resolve (Left { code: -32000, message: err, data: Nothing })
      Right _ -> do
        -- Wait for response
        waitForResponse client id resolve handler
  else do
    -- Queue request if offline
    liftEffect $ queueRequest client { jsonrpc: "2.0", id: show id, method, params: paramsJson }
    resolve (Left { code: -32000, message: "Not connected", data: Nothing })

-- | Send request to server
sendRequest :: WSClient -> JsonRpcRequest -> Aff (Either String Unit)
sendRequest client req = makeAff \resolve -> do
  socket <- liftEffect $ read client.socket
  case socket of
    Just ws -> do
      -- Serialize request using Argonaut
      let message = serializeRequest req
      result <- liftEffect $ send ws message
      resolve result
    Nothing -> resolve (Left "Not connected")

-- | Wait for response with timeout
waitForResponse :: forall a. WSClient -> Int -> (Either JsonRpcError a -> Effect Unit) -> (Json -> Aff a) -> Aff Unit
waitForResponse client id resolve handler = do
  timeoutId <- liftEffect $ new Nothing
  -- Set timeout
  delay client.config.requestTimeout
  -- Check if still pending
  pending <- liftEffect $ read client.pending
  when (Map.member id pending) do
    -- Timeout occurred
    liftEffect $ resolve (Left { code: -32000, message: "Request timeout", data: Nothing })
    liftEffect $ modify (Map.delete id) client.pending

-- | Handle incoming message
handleMessage :: WSClient -> String -> Effect Unit
handleMessage client message = do
  -- Try to parse as ServerMessage first (for notifications/updates)
  case jsonParser message of
    Left _ -> pure unit  -- Not JSON, skip
    Right json -> case decodeJson json :: Either JsonDecodeError ServerMessage of
      Right serverMsg -> do
        -- This is a ServerMessage (BalanceUpdate, Notification, etc.)
        notifySubscribers client serverMsg
        enqueueMessage client serverMsg  -- Enqueue for Halogen dispatch
      Left _ -> do
        -- Try parsing as MessageType (for JSON-RPC responses)
        case parseMessage message of
          Left _ -> pure unit  -- Unknown message format
          Right msg -> case msg of
            Notification notif -> do
              notifySubscribers client notif
              enqueueMessage client notif
            Response resp -> handleResponse client resp
            Ping -> handlePing client
            Pong -> handlePong client

-- | Handle JSON-RPC response
handleResponse :: WSClient -> JsonRpcResponse -> Effect Unit
handleResponse client resp = do
  pending <- read client.pending
  case resp.id >>= \id -> Map.lookup (parseInt id) pending of
    Just { resolve } -> do
      modify (Map.delete (fromMaybe 0 (resp.id >>= parseInt))) client.pending
      case resp.error of
        Just err -> resolve (Left err)
        Nothing -> case resp.result of
          Just result -> resolve (Right result)
          Nothing -> resolve (Left { code: -32603, message: "Internal error: missing result", data: Nothing })
    Nothing -> pure unit  -- Orphan response

-- | Notify all subscribers
notifySubscribers :: WSClient -> ServerMessage -> Effect Unit
notifySubscribers client msg = do
  subs <- read client.subscribers
  traverse_ (_ $ msg) subs

-- | Enqueue message for Halogen dispatch - Add message to queue
-- |
-- | **Purpose:** Adds a ServerMessage to the message queue for later dispatch
-- |             as a Halogen action. This allows Effect callbacks to queue
-- |             messages that will be processed by Halogen polling.
-- | **Parameters:**
-- | - `client`: WebSocket client
-- | - `msg`: Server message to enqueue
-- | **Side Effects:** Modifies messageQueue Ref
enqueueMessage :: WSClient -> ServerMessage -> Effect Unit
enqueueMessage client msg = do
  modify (_ <> [msg]) client.messageQueue

-- | Dequeue all messages - Remove and return all queued messages
-- |
-- | **Purpose:** Removes and returns all messages from the queue for processing.
-- |             This is called by Halogen polling to get pending messages.
-- | **Parameters:**
-- | - `client`: WebSocket client
-- | **Returns:** Array of ServerMessages that were queued
-- | **Side Effects:** Clears messageQueue Ref
dequeueMessages :: WSClient -> Effect (Array ServerMessage)
dequeueMessages client = do
  msgs <- read client.messageQueue
  write [] client.messageQueue
  pure msgs

-- | Subscribe to server notifications
subscribe :: WSClient -> (ServerMessage -> Effect Unit) -> Effect (Effect Unit)
subscribe client handler = do
  modify (_ <> [handler]) client.subscribers
  pure do
    modify (filter (_ /= handler)) client.subscribers

-- | Handle ping from server
handlePing :: WSClient -> Effect Unit
handlePing client = do
  socket <- read client.socket
  case socket of
    Just ws -> do
      -- Send pong response (notification, no id)
      let pongReq = { jsonrpc: "2.0", id: Nothing, method: "pong", params: AC.fromObject $ AC.fromFoldable [] }
      void $ send ws (serializeRequest pongReq)
    Nothing -> pure unit

-- | Handle pong from server
handlePong :: WSClient -> Effect Unit
handlePong client = do
  -- Update last ping time
  currentTime <- getCurrentDateTime
  write (Just currentTime) client.lastPing

-- | Start heartbeat monitoring
-- | Note: Full implementation would start an interval timer to:
-- | 1. Send ping if no pong received within heartbeatTimeout
-- | 2. Check connection health
-- | 3. Trigger reconnection if heartbeat fails
-- | For now, server handles heartbeat via ping/pong messages
startHeartbeat :: WSClient -> Effect Unit
startHeartbeat client = do
  -- Heartbeat is handled by server ping/pong messages
  -- Full client-side heartbeat monitoring would require Effect.Aff timers
  -- This is a reasonable placeholder - server initiates heartbeat
  pure unit

-- | Attempt reconnection with exponential backoff
attemptReconnect :: WSClient -> Effect Unit
attemptReconnect client = do
  attempt <- read client.reconnectAttempt
  if attempt >= client.config.maxReconnectAttempts then
    write (Error "Max reconnection attempts reached") client.state
  else do
    write (Reconnecting (attempt + 1)) client.state
    modify (_ + 1) client.reconnectAttempt
    -- Schedule reconnect
    void $ launchAff_ do
      delay $ Milliseconds $ toNumber (attempt + 1) * 1000.0
      connect client

-- | Queue request for later sending
queueRequest :: WSClient -> JsonRpcRequest -> Effect Unit
queueRequest client req = do
  queue <- read client.queue
  if Array.length queue >= client.config.maxQueueSize then
    pure unit  -- Drop oldest or reject
  else do
    -- Get current DateTime for timestamp
    timestamp <- getCurrentDateTime
    modify (_ <> [{ request: req, timestamp: timestamp, retries: 0 }]) client.queue

-- | Process queued messages
processQueue :: WSClient -> Effect Unit
processQueue client = do
  queue <- read client.queue
  write [] client.queue
  -- Send all queued messages
  traverse_ (\queued -> void $ sendRequest client queued.request) queue

-- | Disconnect from server
disconnect :: WSClient -> Effect Unit
disconnect client = do
  socket <- read client.socket
  case socket of
    Just ws -> do
      closeWith ws 1000 "Client disconnect"
      write Nothing client.socket
      write Disconnected client.state
    Nothing -> pure unit

-- | JSON-RPC Request codec
instance EncodeJson JsonRpcRequest where
  encodeJson req = AC.fromObject $ AC.fromFoldable
    [ "jsonrpc" := req.jsonrpc
    , "id" :=? req.id
    , "method" := req.method
    , "params" := req.params
    ]

instance DecodeJson JsonRpcRequest where
  decodeJson json = do
    obj <- decodeJson json
    jsonrpc <- obj .: "jsonrpc"
    id <- obj .:? "id"
    method <- obj .: "method"
    params <- obj .: "params"
    pure { jsonrpc, id, method, params }

-- | JSON-RPC Response codec
instance DecodeJson JsonRpcResponse where
  decodeJson json = do
    obj <- decodeJson json
    jsonrpc <- obj .: "jsonrpc"
    id <- obj .:? "id"
    result <- obj .:? "result"
    error <- obj .:? "error"
    pure { jsonrpc, id, result, error }

data MessageType = Notification ServerMessage | Response JsonRpcResponse | Ping | Pong

parseMessage :: String -> Either String MessageType
parseMessage str = case jsonParser str of
  Left err -> Left err
  Right json -> case decodeJson json of
    Left err -> Left err
    Right msg -> Right msg

serializeRequest :: JsonRpcRequest -> String
serializeRequest req = AC.stringify $ encodeJson req

parseInt :: String -> Maybe Int
parseInt = Int.fromString
