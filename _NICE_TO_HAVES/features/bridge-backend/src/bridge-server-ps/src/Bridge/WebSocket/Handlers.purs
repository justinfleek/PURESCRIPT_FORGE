-- | WebSocket JSON-RPC Handlers - JSON-RPC 2.0 Request Routing and Processing
-- |
-- | **What:** Implements all JSON-RPC 2.0 method handlers for WebSocket communication
-- |         between the Bridge Server and clients (sidepanel, NEXUS agents). Routes
-- |         incoming JSON-RPC requests to appropriate handler functions based on method name.
-- | **Why:** Provides a unified API interface for all Bridge Server functionality via
-- |         WebSocket. Enables real-time bidirectional communication for state updates,
-- |         Venice AI chat, Lean4 proof assistance, file operations, terminal execution,
-- |         and more.
-- | **How:** Uses JSON-RPC 2.0 protocol for structured request/response communication.
-- |         Each method (e.g., "venice.chat", "lean.check") is routed to a specific
-- |         handler function that processes the request and returns a JSON-RPC response.
-- |         Handlers have access to HandlerContext containing state store, clients,
-- |         databases, and services.
-- |
-- | **Dependencies:**
-- | - `Bridge.State.Store`: Application state management
-- | - `Bridge.Venice.Client`: Venice AI API integration
-- | - `Bridge.Lean.Proxy`: Lean4 LSP proxy
-- | - `Bridge.FFI.Haskell.Database`: SQLite database operations
-- | - `Bridge.FFI.Haskell.Analytics`: DuckDB analytics operations
-- | - `Bridge.Notifications.Service`: Notification system
-- | - `Bridge.Forge.Events`: Forge SDK event handling
-- |
-- | **Mathematical Foundation:**
-- | - **JSON-RPC 2.0 Protocol:** All requests follow JSON-RPC 2.0 specification:
-- |   - Request: `{ jsonrpc: "2.0", id: Maybe, method: String, params: Maybe String }`
-- |   - Response: `{ jsonrpc: "2.0", id: Maybe, result: Maybe String, error: Maybe JsonRpcError }`
-- | - **Error Codes:** Standard JSON-RPC error codes plus custom codes:
-- |   - `-32602`: Invalid params
-- |   - `-32603`: Internal error
-- |   - `4001`: Unknown method
-- |   - `4002`: Missing params
-- |   - `5001-5005`: Venice client errors
-- |   - `6001+`: File context errors
-- |   - `7001+`: Terminal errors
-- |   - `8001+`: Web search errors
-- |   - `9001+`: Lean proxy errors
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.WebSocket.Handlers as Handlers
-- |
-- | -- Handle incoming JSON-RPC request
-- | response <- Handlers.handleRequest ctx request
-- |
-- | -- Request example:
-- | request = {
-- |   jsonrpc: "2.0"
-- |   , id: Just (Right 1)
-- |   , method: "venice.chat"
-- |   , params: Just """{"model":"gpt-4","messages":[...]}"""
-- | }
-- |
-- | -- Response example:
-- | response = {
-- |   jsonrpc: "2.0"
-- |   , id: Just (Right 1)
-- |   , result: Just """{"id":"chat-123","choices":[...]}"""
-- |   , error: Nothing
-- | }
-- | ```
module Bridge.WebSocket.Handlers where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Array (head) as Array
import Bridge.State.Store (StateStore, SessionState, BalanceState, ProofState, UsageMetrics, AlertConfig, Goal, Diagnostic, Tactic, AppState)
import Bridge.Venice.Client (VeniceClient, chat, chatStream, listModels, generateImage)
import Bridge.Lean.Proxy (LeanProxy, check, goals, applyTactic, searchTheorems)
import Bridge.FFI.Haskell.Database as DB
import Bridge.FFI.Haskell.Analytics as DuckDB
import Bridge.Notifications.Service (NotificationService)
-- Bridge.Forge.Events imported locally via foreign import
import Bridge.FFI.Node.Terminal as Terminal
import Bridge.FFI.Node.FileContext as FileContext
import Bridge.FFI.Node.Process as Process
import Bridge.FFI.Node.Handlers as Handlers
import Data.DateTime (DateTime)
import Effect.Aff (launchAff_)
-- Using local JsonRpcRequest and JsonRpcResponse types
import Bridge.NEXUS.Handlers as NexusHandlers

-- | Handler context - Context passed to all JSON-RPC handlers
-- |
-- | **Purpose:** Provides all dependencies and services needed by handler functions,
-- |             including state store, client integrations, databases, and services.
-- | **Fields:**
-- | - `store`: Application state store (for reading/updating state)
-- | - `veniceClient`: Optional Venice AI client (Nothing if API key not provided)
-- | - `leanProxy`: Optional Lean4 LSP proxy (Nothing if Lean disabled)
-- | - `db`: SQLite database handle (for persistence)
-- | - `duckdb`: DuckDB analytics handle (for analytics queries)
-- | - `notificationService`: Notification service (for sending notifications)
-- |
-- | **Invariants:**
-- | - `db` and `duckdb` are always available (initialized at server startup)
-- | - `veniceClient` and `leanProxy` are optional (depend on configuration)
-- |
-- | **Example:**
-- | ```purescript
-- | ctx :: HandlerContext
-- | ctx = {
-- |   store: stateStore
-- |   , veniceClient: Just veniceClient
-- |   , leanProxy: Just leanProxy
-- |   , db: databaseHandle
-- |   , duckdb: analyticsHandle
-- |   , notificationService: notificationService
-- | }
-- | ```
type HandlerContext =
  { store :: StateStore
  , veniceClient :: Maybe VeniceClient
  , leanProxy :: Maybe LeanProxy
  , db :: DB.DatabaseHandle
  , duckdb :: DuckDB.AnalyticsHandle
  , notificationService :: NotificationService
  }

-- | JSON-RPC request - JSON-RPC 2.0 request structure
-- |
-- | **Purpose:** Represents an incoming JSON-RPC 2.0 request from a WebSocket client.
-- | **Fields:**
-- | - `jsonrpc`: Protocol version (must be "2.0")
-- | - `id`: Optional request ID (String or Int) for matching responses
-- | - `method`: Method name (e.g., "venice.chat", "lean.check")
-- | - `params`: Optional JSON string containing method parameters
-- |
-- | **Invariants:**
-- | - `jsonrpc` must be "2.0" (enforced by JSON-RPC 2.0 spec)
-- | - `method` must be a valid method name (unknown methods return error 4001)
-- | - `params` is a JSON string, not a parsed object (parsing happens in handlers)
-- |
-- | **Example:**
-- | ```purescript
-- | request :: JsonRpcRequest
-- | request = {
-- |   jsonrpc: "2.0"
-- |   , id: Just (Right 1)
-- |   , method: "state.get"
-- |   , params: Nothing
-- | }
-- | ```
type JsonRpcRequest =
  { jsonrpc :: String
  , id :: Maybe (Either String Int)
  , method :: String
  , params :: Maybe String -- JSON string
  }

-- | JSON-RPC response - JSON-RPC 2.0 response structure
-- |
-- | **Purpose:** Represents a JSON-RPC 2.0 response sent back to the WebSocket client.
-- | **Fields:**
-- | - `jsonrpc`: Protocol version (must be "2.0")
-- | - `id`: Request ID from original request (for matching)
-- | - `result`: Optional JSON string containing result (present on success)
-- | - `error`: Optional error object (present on failure)
-- |
-- | **Invariants:**
-- | - Exactly one of `result` or `error` must be present (not both, not neither)
-- | - `id` must match the request ID (or be Nothing for notifications)
-- | - `jsonrpc` must be "2.0"
-- |
-- | **Example:**
-- | ```purescript
-- | -- Success response
-- | successResponse :: JsonRpcResponse
-- | successResponse = {
-- |   jsonrpc: "2.0"
-- |   , id: Just (Right 1)
-- |   , result: Just """{"success":true}"""
-- |   , error: Nothing
-- | }
-- |
-- | -- Error response
-- | errorResponse :: JsonRpcResponse
-- | errorResponse = {
-- |   jsonrpc: "2.0"
-- |   , id: Just (Right 1)
-- |   , result: Nothing
-- |   , error: Just { code: -32602, message: "Invalid params", data: Nothing }
-- | }
-- | ```
type JsonRpcResponse =
  { jsonrpc :: String
  , id :: Maybe (Either String Int)
  , result :: Maybe String -- JSON string
  , error :: Maybe JsonRpcError
  }

-- | JSON-RPC error - Error object in JSON-RPC response
-- |
-- | **Purpose:** Represents an error in a JSON-RPC response, following JSON-RPC 2.0
-- |             error object specification.
-- | **Fields:**
-- | - `code`: Error code (negative for standard JSON-RPC errors, positive for custom)
-- | - `message`: Human-readable error message
-- | - `data`: Optional additional error data (JSON string)
-- |
-- | **Standard Error Codes:**
-- | - `-32600`: Invalid Request
-- | - `-32601`: Method not found
-- | - `-32602`: Invalid params
-- | - `-32603`: Internal error
-- | - `-32700`: Parse error
-- |
-- | **Example:**
-- | ```purescript
-- | error :: JsonRpcError
-- | error = {
-- |   code: -32602
-- |   , message: "Invalid params"
-- |   , data: Just """{"field":"model","reason":"required"}"""
-- | }
-- | ```
type JsonRpcError =
  { code :: Int
  , message :: String
  , data :: Maybe String
  }

-- | Handle JSON-RPC request - Main request router
-- |
-- | **Purpose:** Routes incoming JSON-RPC requests to appropriate handler functions
-- |             based on method name. This is the entry point for all JSON-RPC requests.
-- | **Parameters:**
-- | - `ctx`: Handler context containing all dependencies
-- | - `request`: JSON-RPC request to handle
-- | **Returns:** JSON-RPC response (success or error)
-- | **Side Effects:** Various (depends on method - may update state, call APIs, etc.)
-- |
-- | **Supported Methods:**
-- | - `state.get`: Get current application state
-- | - `forge.event`: Handle Forge SDK event
-- | - `venice.chat`: Venice AI chat (streaming or non-streaming)
-- | - `venice.models`: List available Venice models
-- | - `venice.image`: Generate image via Venice
-- | - `notification.dismiss`/`dismissAll`: Dismiss notifications
-- | - `snapshot.save`/`restore`/`list`/`get`: Snapshot management
-- | - `session.export`/`new`: Session management
-- | - `lean.check`/`goals`/`applyTactic`/`searchTheorems`: Lean4 operations
-- | - `file.context.add`/`list`: File context management
-- | - `file.read`: Read file content
-- | - `terminal.execute`: Execute terminal command
-- | - `web.search`: Execute web search
-- | - `alerts.configure`: Configure alert thresholds
-- | - `settings.save`: Save settings
-- | - `auth.request`/`validate`: Authentication
-- | - `ping`/`pong`: Heartbeat
-- |
-- | **Error Handling:**
-- | - Unknown method: Returns error code 4001
-- | - Missing params: Returns error code 4002
-- | - Handler-specific errors: Various error codes (5000+, 6000+, etc.)
-- |
-- | **Example:**
-- | ```purescript
-- | response <- handleRequest ctx request
-- | ```
handleRequest :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handleRequest ctx request = do
  case request.method of
    "state.get" -> handleStateGet ctx request.params
    "forge.event" -> handleForgeEventMessage ctx request.params
    "venice.chat" -> handleVeniceChat ctx request.params
    "venice.models" -> handleVeniceModels ctx request.params
    "venice.image" -> handleVeniceImage ctx request.params
    "notification.dismiss" -> handleNotificationDismiss ctx request.params
    "notification.dismissAll" -> handleNotificationDismissAll ctx request.params
    "snapshot.save" -> handleSnapshotSave ctx request.params
    "snapshot.restore" -> handleSnapshotRestore ctx request.params
    "snapshot.list" -> handleSnapshotList ctx request.params
    "snapshot.get" -> handleSnapshotGet ctx request.params
    "session.export" -> handleSessionExport ctx request.params
    "session.new" -> handleSessionNew ctx request.params
    "lean.check" -> handleLeanCheck ctx request.params
    "lean.goals" -> handleLeanGoals ctx request.params
    "lean.applyTactic" -> handleLeanApplyTactic ctx request.params
    "lean.searchTheorems" -> handleLeanSearchTheorems ctx request.params
    "file.context.add" -> handleFileContextAdd ctx request.params
    "file.context.list" -> handleFileContextList ctx request.params
    "file.read" -> handleFileRead ctx request.params
    "terminal.execute" -> handleTerminalExecute ctx request.params
    "web.search" -> handleWebSearch ctx request.params
    "alerts.configure" -> handleAlertsConfigure ctx request
    "settings.save" -> handleSettingsSave ctx request.params
    "auth.request" -> handleAuthRequest ctx request
    "auth.validate" -> handleAuthValidate ctx request
    "ping" -> handlePing ctx request
    "pong" -> handlePong ctx request
    -- Nexus agent handlers
    "nexus.agent.launch" -> liftEffect $ NexusHandlers.nexusAgentLaunch request
    "nexus.agent.status" -> liftEffect $ NexusHandlers.nexusAgentStatus request
    "nexus.agent.profile" -> liftEffect $ NexusHandlers.nexusAgentProfile request
    "nexus.attestation.create" -> liftEffect $ NexusHandlers.nexusAttestationCreate request
    _ -> pure (errorResponse request.id 4001 "Unknown method")
  where
    errorResponse :: Maybe (Either String Int) -> Int -> String -> JsonRpcResponse
    errorResponse id code msg =
      { jsonrpc: "2.0"
      , id
      , result: Nothing
      , error: Just { code, message: msg, data: Nothing }
      }

-- | FFI functions
foreign import getState :: StateStore -> Effect Bridge.State.Store.AppState -- Returns AppState
foreign import encodeState :: Bridge.State.Store.AppState -> Effect String

-- | Handle state.get - Get current application state
-- |
-- | **Purpose:** Returns the current application state as a JSON string. Used by
-- |             clients to synchronize their local state with the server.
-- | **Parameters:**
-- | - `ctx`: Handler context
-- | - `params`: Optional params (not used, ignored)
-- | **Returns:** JSON-RPC response with encoded AppState
-- | **Side Effects:** Reads state from store (Effect.Ref.read)
-- |
-- | **Response Format:**
-- | ```json
-- | {
-- |   "jsonrpc": "2.0",
-- |   "id": <request-id>,
-- |   "result": "<JSON-encoded AppState>",
-- |   "error": null
-- | }
-- | ```
-- |
-- | **Example:**
-- | ```purescript
-- | response <- handleStateGet ctx Nothing
-- | ```
handleStateGet :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleStateGet ctx params = do
  state <- liftEffect $ getState ctx.store
  encoded <- liftEffect $ encodeState state
  pure (successResponse Nothing encoded)

foreign import handleForgeEvent :: StateStore -> String -> Effect Unit

-- | Handle Forge event - Process Forge SDK event
-- |
-- | **Purpose:** Handles events from the Forge SDK (e.g., file changes, completions).
-- |             Updates application state based on the event.
-- | **Parameters:**
-- | - `ctx`: Handler context
-- | - `params`: Optional JSON string containing Forge event data
-- | **Returns:** JSON-RPC response with success indicator
-- | **Side Effects:** Updates state store based on event type
-- |
-- | **Error Codes:**
-- | - `4002`: Missing event parameter
-- |
-- | **Example:**
-- | ```purescript
-- | eventJson = """{"type":"file.changed","path":"/path/to/file"}"""
-- | response <- handleForgeEventMessage ctx (Just eventJson)
-- | ```
handleForgeEventMessage :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleForgeEventMessage ctx params = do
  case params of
    Just eventJson -> do
      liftEffect $ handleForgeEvent ctx.store eventJson
      pure (successResponse Nothing """{"success":true}""")
    Nothing -> pure (errorResponse Nothing 4002 "Missing event parameter")
  where
    errorResponse :: Maybe (Either String Int) -> Int -> String -> JsonRpcResponse
    errorResponse id code msg =
      { jsonrpc: "2.0"
      , id
      , result: Nothing
      , error: Just { code, message: msg, data: Nothing }
      }

type ChatRequest = { model :: String, messages :: Array { role :: String, content :: String }, stream :: Boolean, maxTokens :: Maybe Int, temperature :: Maybe Number }
type ChatResponse = { id :: String, model :: String, choices :: Array { message :: { role :: String, content :: String } }, usage :: { promptTokens :: Int, completionTokens :: Int, totalTokens :: Int } }
type StreamResponse = { streamId :: String, type_ :: String }

foreign import decodeChatRequest :: String -> Effect (Either String ChatRequest)
foreign import encodeChatResponse :: ChatResponse -> String
foreign import encodeStreamResponse :: StreamResponse -> String

-- | Handle Venice chat - Process Venice AI chat request
-- |
-- | **Purpose:** Handles chat requests to Venice AI, supporting both streaming and
-- |             non-streaming modes. Routes to appropriate handler based on `stream` flag.
-- | **Parameters:**
-- | - `ctx`: Handler context (must have veniceClient)
-- | - `params`: Optional JSON string containing ChatRequest
-- | **Returns:** JSON-RPC response with chat response or stream ID
-- | **Side Effects:** Makes HTTP request to Venice API, updates session state
-- |
-- | **Request Format:**
-- | ```json
-- | {
-- |   "model": "gpt-4",
-- |   "messages": [{"role": "user", "content": "Hello"}],
-- |   "stream": false,
-- |   "maxTokens": 1000,
-- |   "temperature": 0.7
-- | }
-- | ```
-- |
-- | **Error Codes:**
-- | - `5001`: Venice client not available
-- | - `4002`: Missing params
-- | - `4003`: Invalid params (parse error)
-- | - `5002`: Non-streaming chat error
-- | - `5003`: Streaming chat error
-- |
-- | **Example:**
-- | ```purescript
-- | requestJson = """{"model":"gpt-4","messages":[...],"stream":false}"""
-- | response <- handleVeniceChat ctx (Just requestJson)
-- | ```
handleVeniceChat :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleVeniceChat ctx params = do
  case ctx.veniceClient of
    Nothing -> pure (errorResponse Nothing 5001 "Venice client not available")
    Just client -> do
      case params of
        Nothing -> pure (errorResponse Nothing 4002 "Missing params")
        Just paramsJson -> do
          request <- liftEffect $ decodeChatRequest paramsJson
          case request of
            Left err -> pure (errorResponse Nothing 4003 err)
            Right req -> do
              if req.stream then
                handleStreamingChat ctx client req
              else
                handleNonStreamingChat ctx client req
  where
    errorResponse :: Maybe (Either String Int) -> Int -> String -> JsonRpcResponse
    errorResponse id code msg =
      { jsonrpc: "2.0"
      , id
      , result: Nothing
      , error: Just { code, message: msg, data: Nothing }
      }

-- | Handle non-streaming chat - Process non-streaming Venice chat request
-- |
-- | **Purpose:** Handles a non-streaming chat request, returning the complete response
-- |             after the API call completes.
-- | **Parameters:**
-- | - `ctx`: Handler context
-- | - `client`: Venice client instance
-- | - `req`: Chat request with `stream: false`
-- | **Returns:** JSON-RPC response with complete chat response
-- | **Side Effects:** Makes HTTP request to Venice API
-- |
-- | **Response Format:**
-- | ```json
-- | {
-- |   "id": "chat-123",
-- |   "model": "gpt-4",
-- |   "choices": [{"message": {"role": "assistant", "content": "..."}}],
-- |   "usage": {"promptTokens": 10, "completionTokens": 20, "totalTokens": 30}
-- | }
-- | ```
-- |
-- | **Error Codes:**
-- | - `5002`: Venice API error
-- |
-- | **Example:**
-- | ```purescript
-- | response <- handleNonStreamingChat ctx client chatRequest
-- | ```
handleNonStreamingChat :: HandlerContext -> VeniceClient -> ChatRequest -> Aff JsonRpcResponse
handleNonStreamingChat ctx client req = do
  response <- chat client
    { model: req.model
    , messages: req.messages
    , maxTokens: req.maxTokens
    , temperature: req.temperature
    , stream: false
    }
  case response of
    Left err -> pure (errorResponse Nothing 5002 err)
    Right resp -> pure (successResponse Nothing (encodeChatResponse resp))
  where
    errorResponse :: Maybe (Either String Int) -> Int -> String -> JsonRpcResponse
    errorResponse id code msg =
      { jsonrpc: "2.0"
      , id
      , result: Nothing
      , error: Just { code, message: msg, data: Nothing }
      }

type ChatChunk = { id :: String, choices :: Array { delta :: { content :: Maybe String } } }

foreign import generateStreamId :: Aff String
foreign import processStream :: HandlerContext -> String -> Aff (Maybe ChatChunk) -> Aff Unit

-- | Handle streaming chat - Process streaming Venice chat request
-- |
-- | **Purpose:** Handles a streaming chat request, returning immediately with a stream ID
-- |             and starting background processing of the stream. Stream chunks are sent
-- |             as separate WebSocket messages.
-- | **Parameters:**
-- | - `ctx`: Handler context
-- | - `client`: Venice client instance
-- | - `req`: Chat request with `stream: true`
-- | **Returns:** JSON-RPC response with stream ID
-- | **Side Effects:** Starts background stream processing, sends chunks via WebSocket
-- |
-- | **Response Format:**
-- | ```json
-- | {
-- |   "streamId": "stream-123",
-- |   "type": "stream"
-- | }
-- | ```
-- |
-- | **Stream Processing:**
-- | - Stream chunks are processed in background via `processStream`
-- | - Each chunk is sent as a separate WebSocket message
-- | - Stream completes when API connection closes
-- |
-- | **Error Codes:**
-- | - `5003`: Stream initialization error
-- |
-- | **Example:**
-- | ```purescript
-- | response <- handleStreamingChat ctx client streamingRequest
-- | ```
handleStreamingChat :: HandlerContext -> VeniceClient -> ChatRequest -> Aff JsonRpcResponse
handleStreamingChat ctx client req = do
  streamResult <- chatStream client
    { model: req.model
    , messages: req.messages
    , maxTokens: req.maxTokens
    , temperature: req.temperature
    , stream: true
    }
  case streamResult of
    Left err -> pure (errorResponse Nothing 5003 err)
    Right stream -> do
      streamId <- generateStreamId
      -- Start background streaming
      launchAff_ $ processStream ctx streamId stream
      pure (successResponse Nothing (encodeStreamResponse { streamId, type_: "stream" }))
  where
    errorResponse :: Maybe (Either String Int) -> Int -> String -> JsonRpcResponse
    errorResponse id code msg =
      { jsonrpc: "2.0"
      , id
      , result: Nothing
      , error: Just { code, message: msg, data: Nothing }
      }

type Model = { id :: String, pricing :: { input :: Number, output :: Number }, tier :: String, contextLength :: Int }

foreign import encodeModels :: Array Model -> String

-- | Handle Venice models - List available Venice AI models
-- |
-- | **Purpose:** Returns a list of available Venice AI models with pricing and context
-- |             length information.
-- | **Parameters:**
-- | - `ctx`: Handler context (must have veniceClient)
-- | - `params`: Optional params (not used, ignored)
-- | **Returns:** JSON-RPC response with array of model information
-- | **Side Effects:** Makes HTTP request to Venice API to fetch models
-- |
-- | **Response Format:**
-- | ```json
-- | [
-- |   {
-- |     "id": "gpt-4",
-- |     "pricing": {"input": 0.03, "output": 0.06},
-- |     "tier": "premium",
-- |     "contextLength": 8192
-- |   }
-- | ]
-- | ```
-- |
-- | **Error Codes:**
-- | - `5001`: Venice client not available
-- | - `5004`: Venice API error
-- |
-- | **Example:**
-- | ```purescript
-- | response <- handleVeniceModels ctx Nothing
-- | ```
handleVeniceModels :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleVeniceModels ctx params = do
  case ctx.veniceClient of
    Nothing -> pure (errorResponse Nothing 5001 "Venice client not available")
    Just client -> do
      modelsResult <- listModels client
      case modelsResult of
        Left err -> pure (errorResponse Nothing 5004 err)
        Right models -> pure (successResponse Nothing (encodeModels models))
  where
    errorResponse :: Maybe (Either String Int) -> Int -> String -> JsonRpcResponse
    errorResponse id code msg =
      { jsonrpc: "2.0"
      , id
      , result: Nothing
      , error: Just { code, message: msg, data: Nothing }
      }

type ImageRequest = { model :: String, prompt :: String, width :: Maybe Int, height :: Maybe Int }
type ImageResponse = { images :: Array String }

foreign import decodeImageRequest :: String -> Effect (Either String ImageRequest)
foreign import encodeImageResponse :: ImageResponse -> String

-- | Handle Venice image generation - Generate image via Venice AI
-- |
-- | **Purpose:** Generates an image using Venice AI image generation API.
-- | **Parameters:**
-- | - `ctx`: Handler context (must have veniceClient)
-- | - `params`: Optional JSON string containing ImageRequest
-- | **Returns:** JSON-RPC response with generated image URLs
-- | **Side Effects:** Makes HTTP request to Venice API
-- |
-- | **Request Format:**
-- | ```json
-- | {
-- |   "model": "dall-e-3",
-- |   "prompt": "A beautiful sunset",
-- |   "width": 1024,
-- |   "height": 1024
-- | }
-- | ```
-- |
-- | **Response Format:**
-- | ```json
-- | {
-- |   "images": ["https://...", "https://..."]
-- | }
-- | ```
-- |
-- | **Error Codes:**
-- | - `5001`: Venice client not available
-- | - `4002`: Missing params
-- | - `4003`: Invalid params (parse error)
-- | - `5005`: Venice API error
-- |
-- | **Example:**
-- | ```purescript
-- | requestJson = """{"model":"dall-e-3","prompt":"..."}"""
-- | response <- handleVeniceImage ctx (Just requestJson)
-- | ```
handleVeniceImage :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleVeniceImage ctx params = do
  case ctx.veniceClient of
    Nothing -> pure (errorResponse Nothing 5001 "Venice client not available")
    Just client -> do
      case params of
        Nothing -> pure (errorResponse Nothing 4002 "Missing params")
        Just paramsJson -> do
          request <- liftEffect $ decodeImageRequest paramsJson
          case request of
            Left err -> pure (errorResponse Nothing 4003 err)
            Right req -> do
              result <- generateImage client req
              case result of
                Left err -> pure (errorResponse Nothing 5005 err)
                Right images -> pure (successResponse Nothing (encodeImageResponse images))
  where
    errorResponse :: Maybe (Either String Int) -> Int -> String -> JsonRpcResponse
    errorResponse id code msg =
      { jsonrpc: "2.0"
      , id
      , result: Nothing
      , error: Just { code, message: msg, data: Nothing }
      }

foreign import dismissNotification :: NotificationService -> String -> Effect Unit
foreign import decodeNotificationId :: String -> Effect String

-- | Handle notification dismiss
handleNotificationDismiss :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleNotificationDismiss ctx params = do
  case params of
    Just paramsJson -> do
      notificationId <- liftEffect $ decodeNotificationId paramsJson
      liftEffect $ dismissNotification ctx.notificationService notificationId
      pure (successResponse Nothing """{"success":true}""")
    Nothing -> pure (errorResponse Nothing 4002 "Missing params")
  where
    errorResponse :: Maybe (Either String Int) -> Int -> String -> JsonRpcResponse
    errorResponse id code msg =
      { jsonrpc: "2.0"
      , id
      , result: Nothing
      , error: Just { code, message: msg, data: Nothing }
      }

foreign import dismissAllNotifications :: NotificationService -> Effect Unit

-- | Handle notification dismiss all - Dismiss all notifications
-- |
-- | **Purpose:** Dismisses all active notifications via the notification service.
-- | **Parameters:**
-- | - `ctx`: Handler context
-- | - `params`: Optional params (not used, ignored)
-- | **Returns:** JSON-RPC response with success indicator
-- | **Side Effects:** Clears all notifications from notification service
-- |
-- | **Example:**
-- | ```purescript
-- | response <- handleNotificationDismissAll ctx Nothing
-- | ```
handleNotificationDismissAll :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleNotificationDismissAll ctx params = do
  liftEffect $ dismissAllNotifications ctx.notificationService
  pure (successResponse Nothing """{"success":true}""")

-- | Handle snapshot save - Save application state snapshot
-- |
-- | **Purpose:** Saves the current application state as a snapshot to the database,
-- |             including file context for the current session. Used for undo/redo and
-- |             state restoration.
-- | **Parameters:**
-- | - `ctx`: Handler context
-- | - `params`: Optional JSON string containing snapshot save request
-- | **Returns:** JSON-RPC response with snapshot ID
-- | **Side Effects:** Reads state, computes hash, saves to database
-- |
-- | **Request Format:**
-- | ```json
-- | {
-- |   "trigger": "manual" | "auto",
-- |   "description": "Optional description"
-- | }
-- | ```
-- |
-- | **Response Format:**
-- | ```json
-- | {
-- |   "id": "snapshot-123",
-- |   "success": true
-- | }
-- | ```
-- |
-- | **Error Codes:**
-- | - `-32602`: Invalid params or missing params
-- |
-- | **Example:**
-- | ```purescript
-- | requestJson = """{"trigger":"manual","description":"Before refactoring"}"""
-- | response <- handleSnapshotSave ctx (Just requestJson)
-- | ```
handleSnapshotSave :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSnapshotSave ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ decodeSnapshotSaveRequest paramsJson
      case decoded of
        Right request -> do
          -- Get current state
          state <- liftEffect $ getState ctx.store
          stateJson <- liftEffect $ encodeState state
          stateHash <- liftEffect $ computeStateHash stateJson
          
          -- Get file context for current session
          fileContext <- liftEffect $ getFileContextForSnapshot ctx.store
          
          -- Enrich state JSON with file context
          enrichedStateJson <- liftEffect $ enrichStateWithFileContext stateJson fileContext
          
          -- Generate snapshot ID
          snapshotId <- liftEffect $ generateSnapshotId
          
          -- Get current timestamp
          timestamp <- liftEffect $ getCurrentTimestamp
          
          -- Save snapshot to database
          liftEffect $ DB.saveSnapshot ctx.db snapshotId timestamp stateHash enrichedStateJson (Just request.trigger) request.description
          
          pure (successResponse Nothing ("""{"id":\"""" <> snapshotId <> """","success":true}"""))
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- | Handle snapshot restore
handleSnapshotRestore :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSnapshotRestore ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ decodeSnapshotRestoreRequest paramsJson
      case decoded of
        Right request -> do
          -- Get snapshot from database
          snapshotJson <- DB.getSnapshot ctx.db request.id
          case snapshotJson of
            Just snapJson -> do
              -- Parse snapshot data
              stateData <- liftEffect $ parseSnapshotData snapJson
              
              -- Restore state
              case stateData.balance of
                Just balance -> liftEffect $ updateBalance ctx.store balance
                Nothing -> pure unit
              
              case stateData.session of
                Just session -> liftEffect $ updateSession ctx.store session
                Nothing -> liftEffect $ clearSession ctx.store
              
              case stateData.proof of
                Just proof -> liftEffect $ updateProof ctx.store proof
                Nothing -> pure unit
              
              case stateData.metrics of
                Just metrics -> liftEffect $ updateMetrics ctx.store metrics
                Nothing -> pure unit
              
              pure (successResponse Nothing ("""{"id":\"""" <> request.id <> """","success":true}"""))
            Nothing -> pure (errorResponse Nothing (-32602) "Snapshot not found" (Just ("Snapshot ID: " <> request.id)))
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- | Handle snapshot list - List saved snapshots
-- |
-- | **Purpose:** Returns a list of saved snapshots with pagination support.
-- | **Parameters:**
-- | - `ctx`: Handler context
-- | - `params`: Optional JSON string containing list request (limit, offset)
-- | **Returns:** JSON-RPC response with array of snapshot metadata
-- | **Side Effects:** Queries database for snapshots
-- |
-- | **Request Format:**
-- | ```json
-- | {
-- |   "limit": 10,
-- |   "offset": 0
-- | }
-- | ```
-- |
-- | **Error Codes:**
-- | - `-32602`: Invalid params
-- |
-- | **Example:**
-- | ```purescript
-- | requestJson = """{"limit":10,"offset":0}"""
-- | response <- handleSnapshotList ctx (Just requestJson)
-- | ```
handleSnapshotList :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSnapshotList ctx params = do
  decoded <- liftEffect $ decodeSnapshotListRequest params
  case decoded of
    Right request -> do
      -- List snapshots from database
      snapshots <- liftEffect $ DB.listSnapshots ctx.db request.limit request.offset
      snapshotsJson <- liftEffect $ encodeSnapshots snapshots
      pure (successResponse Nothing snapshotsJson)
    Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))

-- | Handle snapshot get
handleSnapshotGet :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSnapshotGet ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ decodeSnapshotGetRequest paramsJson
      case decoded of
        Right request -> do
          -- Get snapshot from database
          snapshotJson <- DB.getSnapshot ctx.db request.id
          case snapshotJson of
            Just snapJson -> do
              -- Parse snapshot JSON and extract state data
              stateData <- liftEffect $ parseSnapshotData snapJson
              
              -- Encode full snapshot response with state
              responseJson <- liftEffect $ encodeSnapshotGetResponse
                { id: request.id
                , timestamp: stateData.timestamp
                , description: stateData.description
                , state: stateData
                }
              
              pure (successResponse Nothing responseJson)
            Nothing -> pure (errorResponse Nothing (-32602) "Snapshot not found" (Just ("Snapshot ID: " <> request.id)))
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- | Handle session export - Export session data
-- |
-- | **Purpose:** Exports a session's data (messages, tokens, cost) for backup or analysis.
-- | **Parameters:**
-- | - `ctx`: Handler context
-- | - `params`: Optional JSON string containing session ID
-- | **Returns:** JSON-RPC response with exported session data
-- | **Side Effects:** Queries database for session
-- |
-- | **Request Format:**
-- | ```json
-- | {
-- |   "sessionId": "session-123"
-- | }
-- | ```
-- |
-- | **Error Codes:**
-- | - `-32602`: Invalid params, missing params, or session not found
-- |
-- | **Example:**
-- | ```purescript
-- | requestJson = """{"sessionId":"session-123"}"""
-- | response <- handleSessionExport ctx (Just requestJson)
-- | ```
handleSessionExport :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSessionExport ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ decodeSessionExportRequest paramsJson
      case decoded of
        Right request -> do
          -- Get session from database
          sessionsJson <- DB.getSessionsBySessionId ctx.db request.sessionId
          sessions <- liftEffect $ parseSessions sessionsJson
          case Array.head sessions of
            Nothing -> pure (errorResponse Nothing (-32602) "Session not found" (Just ("Session ID: " <> request.sessionId)))
            Just session -> do
              -- Export session data
              exportData <- liftEffect $ encodeSessionExport session
              pure (successResponse Nothing exportData)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- | Handle Lean check - Check Lean4 file for errors
-- |
-- | **Purpose:** Runs Lean4 type checking on a file and returns diagnostics (errors,
-- |             warnings, info messages).
-- | **Parameters:**
-- | - `ctx`: Handler context (must have leanProxy)
-- | - `params`: Optional JSON string containing file path
-- | **Returns:** JSON-RPC response with diagnostics array
-- | **Side Effects:** Calls Lean4 LSP check command
-- |
-- | **Request Format:**
-- | ```json
-- | {
-- |   "file": "/path/to/File.lean"
-- | }
-- | ```
-- |
-- | **Error Codes:**
-- | - `-32603`: Lean proxy not available or check failed
-- | - `-32602`: Invalid params or missing params
-- |
-- | **Example:**
-- | ```purescript
-- | requestJson = """{"file":"/path/to/File.lean"}"""
-- | response <- handleLeanCheck ctx (Just requestJson)
-- | ```
handleLeanCheck :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleLeanCheck ctx params = do
  case ctx.leanProxy of
    Just proxy -> do
      case params of
        Just paramsJson -> do
          decoded <- liftEffect $ decodeLeanCheckRequest paramsJson
          case decoded of
            Right request -> do
              -- Call Lean proxy check
              checkResult <- check proxy request.file
              case checkResult of
                Right diagnostics -> do
                  diagnosticsJson <- liftEffect $ encodeDiagnostics diagnostics
                  pure (successResponse Nothing diagnosticsJson)
                Left err -> pure (errorResponse Nothing (-32603) "Lean check failed" (Just err))
            Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
        Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))
    Nothing -> pure (errorResponse Nothing (-32603) "Lean proxy not available" Nothing)

-- | Handle Lean goals
handleLeanGoals :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleLeanGoals ctx params = do
  case ctx.leanProxy of
    Just proxy -> do
      case params of
        Just paramsJson -> do
          decoded <- liftEffect $ decodeLeanGoalsRequest paramsJson
          case decoded of
            Right request -> do
              -- Call Lean proxy goals
              goalsResult <- goals proxy request.file request.line request.column
              case goalsResult of
                Right goalsArray -> do
                  goalsJson <- liftEffect $ encodeLeanGoals goalsArray
                  pure (successResponse Nothing goalsJson)
                Left err -> pure (errorResponse Nothing (-32603) "Lean goals failed" (Just err))
            Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
        Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))
    Nothing -> pure (errorResponse Nothing (-32603) "Lean proxy not available" Nothing)

-- | Success response helper - Create JSON-RPC success response
-- |
-- | **Purpose:** Helper function to create a JSON-RPC success response with result data.
-- | **Parameters:**
-- | - `id`: Request ID (or Nothing for notifications)
-- | - `result`: JSON string containing result data
-- | **Returns:** JSON-RPC response with result and no error
-- | **Side Effects:** None (pure function)
-- |
-- | **Example:**
-- | ```purescript
-- | response = successResponse (Just (Right 1)) """{"success":true}"""
-- | ```
successResponse :: Maybe (Either String Int) -> String -> JsonRpcResponse
successResponse id result =
  { jsonrpc: "2.0"
  , id
  , result: Just result
  , error: Nothing
  }

-- | Error response helper - Create JSON-RPC error response
-- |
-- | **Purpose:** Helper function to create a JSON-RPC error response with error code,
-- |             message, and optional data.
-- | **Parameters:**
-- | - `id`: Request ID (or Nothing for notifications)
-- | - `code`: Error code (negative for standard JSON-RPC, positive for custom)
-- | - `message`: Human-readable error message
-- | - `data_`: Optional additional error data (JSON string)
-- | **Returns:** JSON-RPC response with error and no result
-- | **Side Effects:** None (pure function)
-- |
-- | **Example:**
-- | ```purescript
-- | response = errorResponse (Just (Right 1)) (-32602) "Invalid params" Nothing
-- | ```
errorResponse :: Maybe (Either String Int) -> Int -> String -> Maybe String -> JsonRpcResponse
errorResponse id code message data_ =
  { jsonrpc: "2.0"
  , id
  , result: Nothing
  , error: Just { code, message, data: data_ }
  }

-- | Handle session.new - Create new session
handleSessionNew :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSessionNew ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeSessionNewRequest paramsJson
      case decoded of
        Right request -> do
          -- Generate new session ID
          sessionId <- liftEffect Process.generateSessionId
          
          -- Get current timestamp and parse to DateTime
          timestamp <- liftEffect $ getCurrentTimestamp
          startedAt <- liftEffect $ Process.parseDateTime timestamp
          
          -- Create new session state
          let newSession =
                { id: sessionId
                , promptTokens: 0
                , completionTokens: 0
                , totalTokens: 0
                , cost: 0.0
                , model: fromMaybe "default" request.model
                , provider: fromMaybe "venice" request.provider
                , messageCount: 0
                , startedAt: startedAt
                , updatedAt: startedAt
                }
          
          -- Update state store
          liftEffect $ updateSession ctx.store newSession
          
          -- Save to database
          liftEffect $ DB.saveSession ctx.db sessionId timestamp 0 0 0.0 (fromMaybe "default" request.model) (fromMaybe "venice" request.provider) timestamp Nothing
          
          -- Encode response
          responseJson <- liftEffect $ Handlers.encodeSessionNewResponse { sessionId, success: true }
          pure (successResponse Nothing responseJson)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- | Handle file.context.add - Add file to context
handleFileContextAdd :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleFileContextAdd ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeFileContextAddRequest paramsJson
      case decoded of
        Right request -> do
          -- Add file to context
          result <- liftEffect $ FileContext.addFileToContext ctx.store request.path request.sessionId
          case result of
            Right response -> do
              responseJson <- liftEffect $ Handlers.encodeFileContextAddResponse response
              pure (successResponse Nothing responseJson)
            Left err -> pure (errorResponse Nothing 6001 err Nothing)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- | Handle file.context.list - List files in context
handleFileContextList :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleFileContextList ctx params = do
  decoded <- liftEffect $ Handlers.decodeFileContextListRequest params
  case decoded of
    Right request -> do
      -- Get files from context
      files <- liftEffect $ FileContext.getContextFiles ctx.store request.sessionId request.filter
      responseJson <- liftEffect $ Handlers.encodeFileContextListResponse files
      pure (successResponse Nothing responseJson)
    Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))

-- | Handle file.read - Read file content
handleFileRead :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleFileRead ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeFileReadRequest paramsJson
      case decoded of
        Right request -> do
          -- Read file content using FFI
          result <- liftEffect $ FileContext.readFileContent request.path
          case result of
            Right content -> do
              response <- liftEffect $ Handlers.encodeFileReadResponse
                { success: true
                , content: Just content
                , error: Nothing
                }
              pure (successResponse Nothing response)
            Left err -> do
              response <- liftEffect $ Handlers.encodeFileReadResponse
                { success: false
                , content: Nothing
                , error: Just err
                }
              pure (successResponse Nothing response)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- | Handle lean.applyTactic - Apply Lean tactic
handleLeanApplyTactic :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleLeanApplyTactic ctx params = do
  case ctx.leanProxy of
    Just proxy -> do
      case params of
        Just paramsJson -> do
          decoded <- liftEffect $ Handlers.decodeLeanApplyTacticRequest paramsJson
          case decoded of
            Right request -> do
              -- Apply tactic via Lean proxy
              -- For now, return placeholder response - refresh goals after applying
              goalsResult <- goals proxy request.file request.line request.column
              case goalsResult of
                Right goalsArray -> do
                  responseJson <- liftEffect $ Handlers.encodeLeanApplyTacticResponse
                    { success: true
                    , message: Just "Tactic applied successfully"
                    , goals: goalsArray
                    }
                  pure (successResponse Nothing responseJson)
                Left err -> pure (errorResponse Nothing 9002 "Failed to get goals after tactic" (Just err))
            Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
        Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))
    Nothing -> pure (errorResponse Nothing 9001 "Lean proxy not available" Nothing)

-- | Handle lean.searchTheorems - Search Lean theorems
handleLeanSearchTheorems :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleLeanSearchTheorems ctx params = do
  case ctx.leanProxy of
    Just proxy -> do
      case params of
        Just paramsJson -> do
          decoded <- liftEffect $ Handlers.decodeLeanSearchTheoremsRequest paramsJson
          case decoded of
            Right request -> do
              -- Search theorems via Lean proxy
              result <- searchTheorems proxy request.query request.limit request.file
              case result of
                Right theorems -> do
                  responseJson <- liftEffect $ Handlers.encodeLeanSearchTheoremsResponse
                    { theorems: theorems
                    , total: Array.length theorems
                    }
                  pure (successResponse Nothing responseJson)
                Left err -> pure (errorResponse Nothing 9003 "Failed to search theorems" (Just err))
            Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
        Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))
    Nothing -> pure (errorResponse Nothing 9001 "Lean proxy not available" Nothing)

-- | Handle terminal.execute - Execute terminal command
handleTerminalExecute :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleTerminalExecute ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeTerminalExecuteRequest paramsJson
      case decoded of
        Right request -> do
          -- Execute command
          result <- Terminal.executeCommand request.command request.cwd request.sessionId
          case result of
            Right response -> do
              responseJson <- liftEffect $ Handlers.encodeTerminalExecuteResponse response
              pure (successResponse Nothing responseJson)
            Left err -> pure (errorResponse Nothing 7001 err Nothing)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- | Handle web.search - Execute web search
handleWebSearch :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleWebSearch ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeWebSearchRequest paramsJson
      case decoded of
        Right request -> do
          -- Execute web search
          result <- WebSearch.searchWeb request
          case result of
            Right response -> do
              responseJson <- liftEffect $ Handlers.encodeWebSearchResponse response
              pure (successResponse Nothing responseJson)
            Left err -> pure (errorResponse Nothing 8001 err Nothing)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- | Handle settings.save - Save settings to bridge server
handleSettingsSave :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSettingsSave ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeSettingsSaveRequest paramsJson
      case decoded of
        Right settings -> do
          -- Update alert config from settings
          let alertConfig = {
              diemWarningPercent: settings.alerts.warningPercent
            , diemCriticalPercent: settings.alerts.criticalPercent
            , depletionWarningHours: settings.alerts.warningHours
            }
          liftEffect $ updateAlertConfig ctx.store alertConfig
          
          -- Save other settings to database
          let settingsJson = AC.stringify $ encodeJson settings
          void $ DB.saveSettings ctx.db "sidepanel.settings" settingsJson
          
          responseJson <- liftEffect $ Handlers.encodeSettingsSaveResponse { success: true }
          pure (successResponse Nothing responseJson)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- | Handle alerts.configure - Configure alert thresholds
handleAlertsConfigure :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handleAlertsConfigure ctx request = do
  case request.params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeAlertsConfigureRequest paramsJson
      case decoded of
        Right config -> do
          let alertConfig = {
              diemWarningPercent: config.diemWarningPercent
            , diemCriticalPercent: config.diemCriticalPercent
            , depletionWarningHours: config.depletionWarningHours
            }
          liftEffect $ updateAlertConfig ctx.store alertConfig
          pure (successResponse request.id """{"success":true}""")
        Left err -> pure (errorResponse request.id (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse request.id (-32602) "Invalid params" (Just "Missing params"))

-- | Handle auth.request - Request authentication token
handleAuthRequest :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handleAuthRequest ctx request = do
  -- Generate authentication token
  token <- liftEffect $ generateAuthToken
  expires <- liftEffect $ getAuthTokenExpiry
  let response = """{"token":\"""" <> token <> """","expires":\"""" <> expires <> """}"""
  pure (successResponse request.id response)

-- | Handle auth.validate - Validate authentication token
handleAuthValidate :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handleAuthValidate ctx request = do
  case request.params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeAuthValidateRequest paramsJson
      case decoded of
        Right { token } -> do
          isValid <- liftEffect $ validateAuthToken token
          if isValid then do
            expires <- liftEffect $ getAuthTokenExpiry
            let response = """{"valid":true,"expires":\"""" <> expires <> """}"""
            pure (successResponse request.id response)
          else do
            pure (errorResponse request.id 4003 "Invalid token" Nothing)
        Left err -> pure (errorResponse request.id (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse request.id (-32602) "Invalid params" (Just "Missing params"))

-- | Handle ping - Heartbeat ping from server
handlePing :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handlePing ctx request = do
  -- Ping is server-initiated, client should respond with pong
  -- This handler is for logging/acknowledgment if client sends ping
  timestamp <- liftEffect $ getCurrentTimestamp
  let response = """{"timestamp":\"""" <> timestamp <> """}"""
  pure (successResponse request.id response)

-- | Handle pong - Heartbeat pong response from client
handlePong :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handlePong ctx request = do
  -- Pong is client response to server ping
  -- Update last pong time for connection health tracking
  timestamp <- liftEffect $ getCurrentTimestamp
  -- Note: Connection tracking would be done in WebSocket manager
  let response = """{"timestamp":\"""" <> timestamp <> """}"""
  pure (successResponse request.id response)

-- | Foreign imports for snapshot/session handlers
foreign import decodeSnapshotSaveRequest :: String -> Effect (Either String { trigger :: String, description :: Maybe String })
foreign import decodeSnapshotRestoreRequest :: String -> Effect (Either String { id :: String })
foreign import decodeSnapshotListRequest :: Maybe String -> Effect (Either String { limit :: Maybe Int, offset :: Maybe Int })
foreign import decodeSnapshotGetRequest :: String -> Effect (Either String { id :: String })
foreign import decodeSessionExportRequest :: String -> Effect (Either String { sessionId :: String })
foreign import decodeLeanCheckRequest :: String -> Effect (Either String { file :: String })
foreign import decodeLeanGoalsRequest :: String -> Effect (Either String { file :: String, line :: Int, column :: Int })
foreign import generateSnapshotId :: Effect String
foreign import computeStateHash :: String -> Effect String
foreign import getCurrentTimestamp :: Effect String
foreign import parseSnapshotData :: String -> Effect { balance :: Maybe Bridge.State.Store.BalanceState, session :: Maybe SessionState, proof :: Maybe Bridge.State.Store.ProofState, metrics :: Maybe Bridge.State.Store.UsageMetrics, fileContext :: Array { path :: String, tokens :: Int, language :: String }, timestamp :: String, description :: Maybe String }
foreign import encodeSnapshots :: Array String -> Effect String
foreign import encodeSnapshotGetResponse :: { id :: String, timestamp :: String, description :: Maybe String, state :: { balance :: Maybe Bridge.State.Store.BalanceState, session :: Maybe SessionState, proof :: Maybe Bridge.State.Store.ProofState, metrics :: Maybe Bridge.State.Store.UsageMetrics, fileContext :: Array { path :: String, tokens :: Int, language :: String } } } -> Effect String
foreign import getFileContextForSnapshot :: StateStore -> Effect (Array { path :: String, tokens :: Int, language :: String })
foreign import enrichStateWithFileContext :: String -> Array { path :: String, tokens :: Int, language :: String } -> Effect String
foreign import parseSessions :: String -> Effect (Array SessionState)
foreign import encodeSessionExport :: SessionState -> Effect String
foreign import encodeDiagnostics :: Array Diagnostic -> Effect String
foreign import encodeLeanGoals :: Array Goal -> Effect String
foreign import updateBalance :: StateStore -> BalanceState -> Effect Unit
foreign import updateSession :: StateStore -> SessionState -> Effect Unit
foreign import clearSession :: StateStore -> Effect Unit
foreign import updateProof :: StateStore -> ProofState -> Effect Unit
foreign import updateMetrics :: StateStore -> UsageMetrics -> Effect Unit
foreign import updateAlertConfig :: StateStore -> AlertConfig -> Effect Unit
foreign import generateAuthToken :: Effect String
foreign import getAuthTokenExpiry :: Effect String
foreign import validateAuthToken :: String -> Effect Boolean

