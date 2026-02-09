-- | Comprehensive WebSocket Client with JSON-RPC 2.0
-- | Based on spec 31-WEBSOCKET-PROTOCOL.md
module Sidepanel.WebSocket.Client where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, makeAff, delay, Milliseconds(..), launchAff_)
import Effect.Aff.Class (class MonadAff)
import Effect.Ref (Ref, new, read, write, modify)
import Effect.Class (liftEffect)
import Data.Array (filter)
import Data.Array as Array
import Data.Foldable (traverse_)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Either (Either(..))
import Data.Int (toNumber)
import Data.Int as Int
import Data.Number (pow)
import Data.DateTime (DateTime)
import Effect.Exception (Error, error)
import Sidepanel.FFI.Math (random)
import Sidepanel.FFI.WebSocket (WebSocketConnection, create, send, close, closeWith, onOpen, onClose, onError, onMessage)
import Sidepanel.Api.Types (JsonRpcRequest, JsonRpcResponse, JsonRpcError, ServerMessage, decodeJsonRpcError)
import Data.Argonaut.Decode.Error (JsonDecodeError)
import Sidepanel.FFI.DateTime (getCurrentDateTime, toTimestamp)
import Data.Argonaut.Core (Json)
import Data.Argonaut.Core as AC
import Data.Argonaut.Encode (class EncodeJson, encodeJson, (:=))
import Data.Argonaut.Decode (class DecodeJson, decodeJson, (.:), (.:?))
import Data.Argonaut.Parser (jsonParser)
import Foreign.Object as FO

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
  { socket :: Ref (Maybe WebSocketConnection)
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
  socket <- new Nothing
  state <- new Disconnected
  nextId <- new 1
  pending <- new Map.empty
  queue <- new []
  subscribers <- new []
  messageQueue <- new []  -- Initialize message queue for Halogen dispatch
  lastPing <- new Nothing
  reconnectAttempt <- new 0
  pure
    { socket
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
connect :: WSClient -> Aff Unit
connect client = makeAff \resolve -> do
  write Connecting client.state
  socket <- create client.config.url
  setupHandlers client socket resolve
  pure mempty

setupHandlers :: WSClient -> WebSocketConnection -> (Either Error Unit -> Effect Unit) -> Effect Unit
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
    resolve (Left (error errorMsg))

  onMessage socket \message -> do
    handleMessage client message

  write (Just socket) client.socket

-- | Authenticate with server
authenticate :: WSClient -> Effect Unit
authenticate client = case client.config.authToken of
  Just token -> do
    -- Send auth request with proper JSON encoding
    launchAff_ $ void $ request client "auth.request" (AC.fromObject $ FO.fromFoldable [ "token" := token ]) \result -> do
      -- Handle auth response
      pure unit
  Nothing -> pure unit

-- | Send JSON-RPC request and await response
request :: forall a. WSClient -> String -> Json -> (Json -> Aff a) -> Aff (Either JsonRpcError a)
request client method paramsJson handler = do
  id <- liftEffect do
    void $ modify (_ + 1) client.nextId
    read client.nextId
  state <- liftEffect $ read client.state

  if state == Connected then do
    -- Create request with JSON params
    let req = { jsonrpc: "2.0", id: Just (show id), method, params: paramsJson }

    -- Send request
    result <- sendRequest client req

    case result of
      Left err -> pure (Left { code: -32000, message: err, errorData: Nothing })
      Right _ -> do
        -- Wait for response (timeout)
        waitForResponse client id handler
  else do
    -- Queue request if offline
    liftEffect $ queueRequest client { jsonrpc: "2.0", id: Just (show id), method, params: paramsJson }
    pure (Left { code: -32000, message: "Not connected", errorData: Nothing })

-- | Send request to server
sendRequest :: WSClient -> JsonRpcRequest -> Aff (Either String Unit)
sendRequest client req = do
  socketMaybe <- liftEffect $ read client.socket
  case socketMaybe of
    Just ws -> do
      _ <- liftEffect $ send ws (serializeRequest req)
      pure (Right unit)
    Nothing -> pure (Left "Not connected")

-- | Wait for response with timeout
waitForResponse :: forall a. WSClient -> Int -> (Json -> Aff a) -> Aff (Either JsonRpcError a)
waitForResponse client id handler = do
  -- Set timeout
  delay client.config.requestTimeout
  -- Check if still pending
  pending <- liftEffect $ read client.pending
  if Map.member id pending then do
    -- Timeout occurred
    liftEffect $ void $ modify (Map.delete id) client.pending
    pure (Left { code: -32000, message: "Request timeout", errorData: Nothing })
  else
    -- Response was already handled
    pure (Left { code: -32000, message: "Response handled externally", errorData: Nothing })

-- | Handle incoming message
handleMessage :: WSClient -> String -> Effect Unit
handleMessage client message = do
  -- Try to parse as ServerMessage first (for notifications/updates)
  case jsonParser message of
    Left _ -> pure unit  -- Invalid JSON, ignore
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
            MtNotification notif -> do
              notifySubscribers client notif
              enqueueMessage client notif
            MtResponse resp -> handleResponse client resp
            MtPing -> handlePing client
            MtPong -> handlePong client

-- | Handle JSON-RPC response
handleResponse :: WSClient -> JsonRpcResponse -> Effect Unit
handleResponse client resp = do
  pending <- read client.pending
  case resp.id >>= parseInt >>= \intId -> Map.lookup intId pending of
    Just { resolve } -> do
      let deleteId = fromMaybe 0 (resp.id >>= parseInt)
      void $ modify (Map.delete deleteId) client.pending
      case resp.error of
        Just err -> resolve (Left err)
        Nothing -> case resp.result of
          Just result -> resolve (Right result)
          Nothing -> resolve (Left { code: -32603, message: "Internal error: missing result", errorData: Nothing })
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
  void $ modify (_ <> [msg]) client.messageQueue

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
-- | Returns an unsubscribe effect. Uses array length as a simple marker.
subscribe :: WSClient -> (ServerMessage -> Effect Unit) -> Effect (Effect Unit)
subscribe client handler = do
  subs <- read client.subscribers
  let idx = Array.length subs
  write (Array.snoc subs handler) client.subscribers
  pure do
    -- Remove by rebuilding without the handler at the insertion index
    current <- read client.subscribers
    write (Array.deleteAt idx current # fromMaybe current) client.subscribers

-- | Handle ping from server
handlePing :: WSClient -> Effect Unit
handlePing client = do
  socket <- read client.socket
  case socket of
    Just ws -> do
      -- Send pong response (notification, no id)
      let pongReq = { jsonrpc: "2.0", id: Nothing, method: "pong", params: AC.fromObject $ FO.fromFoldable [] }
      void $ send ws (serializeRequest pongReq)
    Nothing -> pure unit

-- | Handle pong from server
handlePong :: WSClient -> Effect Unit
handlePong client = do
  -- Update last ping time
  currentTime <- getCurrentDateTime
  write (Just currentTime) client.lastPing

-- | Start heartbeat monitoring
-- | Server handles heartbeat via WebSocket ping/pong frames.
-- | Client-side monitoring defers to the server-initiated ping/pong protocol,
-- | with reconnection handled by the exponential backoff logic in attemptReconnect.
startHeartbeat :: WSClient -> Effect Unit
startHeartbeat client = do
  -- Server sends ping frames; browser WebSocket auto-replies with pong.
  -- Connection loss is detected by the onclose/onerror handlers
  -- which trigger attemptReconnect with exponential backoff.
  pure unit

-- | Attempt reconnection with exponential backoff and jitter
-- |
-- | **Purpose:** Attempts to reconnect to the WebSocket server using exponential backoff
-- |             with jitter to prevent thundering herd problems. Implements the strategy
-- |             from spec 31-WEBSOCKET-PROTOCOL.md.
-- | **Parameters:**
-- | - `client`: WebSocket client
-- | **Side Effects:** Modifies connection state and schedules reconnection
-- |
-- | **Backoff Strategy:**
-- | - Base delay: `reconnectInterval` (default 1000ms)
-- | - Exponential: `baseDelay * 2^attempt`
-- | - Jitter: Random value between 0 and 1000ms
-- | - Max delay: 30 seconds
-- | - Max attempts: `maxReconnectAttempts` (default 10)
attemptReconnect :: WSClient -> Effect Unit
attemptReconnect client = do
  attempt <- read client.reconnectAttempt
  if attempt >= client.config.maxReconnectAttempts then
    write (Error "Max reconnection attempts reached") client.state
  else do
    write (Reconnecting (attempt + 1)) client.state
    void $ modify (_ + 1) client.reconnectAttempt
    
    -- Calculate exponential backoff with jitter
    void $ launchAff_ do
      baseDelayMs <- liftEffect $ case client.config.reconnectInterval of
        Milliseconds ms -> pure ms
      -- Exponential: baseDelay * 2^attempt
      let exponentialDelay = baseDelayMs * pow 2.0 (toNumber attempt)
      -- Jitter: random between 0 and 1000ms
      jitter <- liftEffect random
      let jitterMs = jitter * 1000.0
      -- Total delay with max cap of 30 seconds
      let totalDelayMs = min (exponentialDelay + jitterMs) 30000.0
      
      -- Schedule reconnect
      delay $ Milliseconds totalDelayMs
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
    void $ modify (_ <> [{ request: req, timestamp: timestamp, retries: 0 }]) client.queue

-- | Process queued messages
processQueue :: WSClient -> Effect Unit
processQueue client = do
  queue <- read client.queue
  write [] client.queue
  -- Send all queued messages
  launchAff_ $ traverse_ (\queued -> void $ sendRequest client queued.request) queue

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

-- | Standalone encoder for JsonRpcRequest (type alias cannot have typeclass instances)
encodeJsonRpcRequest :: JsonRpcRequest -> Json
encodeJsonRpcRequest req = AC.fromObject $ FO.fromFoldable $
    [ "jsonrpc" := req.jsonrpc
    , "method" := req.method
    , "params" := req.params
    ] <> case req.id of
      Just i -> [ "id" := i ]
      Nothing -> []

-- | Standalone decoder for JsonRpcRequest (type alias cannot have typeclass instances)
decodeJsonRpcRequest :: Json -> Either JsonDecodeError JsonRpcRequest
decodeJsonRpcRequest json = do
    obj <- decodeJson json
    jsonrpc <- obj .: "jsonrpc"
    id <- obj .:? "id"
    method <- obj .: "method"
    params <- obj .: "params"
    pure { jsonrpc, id, method, params }

-- | Standalone decoder for JsonRpcResponse (type alias cannot have typeclass instances)
-- | Handles the error field using the standalone decodeJsonRpcError from Types
decodeJsonRpcResponse :: Json -> Either JsonDecodeError JsonRpcResponse
decodeJsonRpcResponse json = do
    obj <- decodeJson json
    jsonrpc <- obj .: "jsonrpc"
    id <- obj .:? "id"
    result <- obj .:? "result"
    -- Manually decode the error field using the standalone decoder
    -- to correctly map JSON "data" key to errorData field
    errorJson <- obj .:? "error"
    error <- case errorJson of
      Nothing -> pure Nothing
      Just ej -> case decodeJsonRpcError ej of
        Right e -> pure (Just e)
        Left err -> Left err
    pure { jsonrpc, id, result, error }

data MessageType = MtNotification ServerMessage | MtResponse JsonRpcResponse | MtPing | MtPong

-- | Parse a WebSocket message string into a MessageType
parseMessage :: String -> Either String MessageType
parseMessage str = case jsonParser str of
  Left err -> Left err
  Right json ->
    -- Try parsing as JSON-RPC response first (has "jsonrpc" field)
    case decodeJsonRpcResponse json of
      Right resp -> Right (MtResponse resp)
      Left _ ->
        -- Try parsing as ServerMessage
        case (decodeJson json :: Either JsonDecodeError ServerMessage) of
          Right msg -> Right (MtNotification msg)
          Left decodeErr -> Left (show decodeErr)

serializeRequest :: JsonRpcRequest -> String
serializeRequest req = AC.stringify $ encodeJsonRpcRequest req

parseInt :: String -> Maybe Int
parseInt = Int.fromString
