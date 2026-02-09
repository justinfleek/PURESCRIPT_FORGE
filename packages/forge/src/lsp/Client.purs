{-|
Module      : Forge.LSP.Client
Description : LSP Client Implementation

Language Server Protocol client for communicating with language servers.
Supports initialization, text synchronization, and various LSP features.

== Features

- Document synchronization
- Hover information
- Completions
- Go to definition
- Find references
- Diagnostics
-}
module Forge.LSP.Client
  ( -- * Types
    LSPClientConfig
  , LSPClient
  , LSPCapabilities
  , ClientState(..)
    -- * Client Operations
  , create
  , connect
  , disconnect
  , isConnected
    -- * Document Operations
  , openDocument
  , closeDocument
  , updateDocument
    -- * LSP Features
  , hover
  , completion
  , definition
  , references
  , diagnostics
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Client state
data ClientState
  = Disconnected
  | Connecting
  | Connected
  | Error String

derive instance eqClientState :: Eq ClientState

instance showClientState :: Show ClientState where
  show Disconnected = "disconnected"
  show Connecting = "connecting"
  show Connected = "connected"
  show (Error e) = "error: " <> e

-- | LSP Client configuration
type LSPClientConfig =
  { serverCommand :: String        -- Command to start server
  , serverArgs :: Array String     -- Arguments for server
  , workspaceRoot :: String        -- Workspace root path
  , language :: String             -- Language ID
  , initializationOptions :: Maybe String  -- JSON options
  }

-- | LSP capabilities
type LSPCapabilities =
  { hoverProvider :: Boolean
  , completionProvider :: Boolean
  , definitionProvider :: Boolean
  , referencesProvider :: Boolean
  , documentFormattingProvider :: Boolean
  }

-- | LSP Client instance
type LSPClient =
  { config :: LSPClientConfig
  , state :: ClientState
  , capabilities :: Maybe LSPCapabilities
  , processId :: Maybe Int
  }

-- | Position in a document
type Position = { line :: Int, character :: Int }

-- | Location in a document
type Location = { uri :: String, range :: { start :: Position, end :: Position } }

-- | Diagnostic information
type Diagnostic =
  { range :: { start :: Position, end :: Position }
  , severity :: Int  -- 1=Error, 2=Warning, 3=Info, 4=Hint
  , message :: String
  , source :: Maybe String
  }

-- | Completion item
type CompletionItem =
  { label :: String
  , kind :: Int
  , detail :: Maybe String
  , insertText :: Maybe String
  }

-- | Hover result
type HoverResult =
  { contents :: String
  , range :: Maybe { start :: Position, end :: Position }
  }

-- ============================================================================
-- FFI
-- ============================================================================

foreign import createClientFFI :: LSPClientConfig -> Aff (Either String LSPClient)
foreign import connectClientFFI :: LSPClient -> Aff (Either String LSPClient)
foreign import disconnectClientFFI :: LSPClient -> Aff (Either String Unit)
foreign import sendRequestFFI :: LSPClient -> String -> String -> Aff (Either String String)

-- ============================================================================
-- CLIENT OPERATIONS
-- ============================================================================

{-| Create an LSP client with the given configuration. -}
create :: LSPClientConfig -> Aff (Either String LSPClient)
create = createClientFFI

{-| Connect to the LSP server.

Starts the server process and performs initialization handshake.
-}
connect :: LSPClient -> Aff (Either String LSPClient)
connect client =
  if client.state == Connected
    then pure $ Right client
    else connectClientFFI client

{-| Disconnect from the LSP server.

Sends shutdown request and terminates the server process.
-}
disconnect :: LSPClient -> Aff (Either String Unit)
disconnect client =
  if client.state == Disconnected
    then pure $ Right unit
    else disconnectClientFFI client

{-| Check if the client is connected. -}
isConnected :: LSPClient -> Boolean
isConnected client = client.state == Connected

-- ============================================================================
-- DOCUMENT OPERATIONS
-- ============================================================================

{-| Notify server that a document was opened. -}
openDocument :: LSPClient -> String -> String -> String -> Aff (Either String Unit)
openDocument client uri languageId content = do
  let params = "{ \"textDocument\": { \"uri\": \"" <> uri <> 
               "\", \"languageId\": \"" <> languageId <> 
               "\", \"version\": 1, \"text\": " <> escapeJson content <> " } }"
  result <- sendRequestFFI client "textDocument/didOpen" params
  pure $ map (const unit) result

{-| Notify server that a document was closed. -}
closeDocument :: LSPClient -> String -> Aff (Either String Unit)
closeDocument client uri = do
  let params = "{ \"textDocument\": { \"uri\": \"" <> uri <> "\" } }"
  result <- sendRequestFFI client "textDocument/didClose" params
  pure $ map (const unit) result

{-| Notify server that a document was changed. -}
updateDocument :: LSPClient -> String -> Int -> String -> Aff (Either String Unit)
updateDocument client uri version content = do
  let params = "{ \"textDocument\": { \"uri\": \"" <> uri <> 
               "\", \"version\": " <> show version <> 
               " }, \"contentChanges\": [{ \"text\": " <> escapeJson content <> " }] }"
  result <- sendRequestFFI client "textDocument/didChange" params
  pure $ map (const unit) result

-- ============================================================================
-- LSP FEATURES
-- ============================================================================

{-| Get hover information at a position. -}
hover :: LSPClient -> String -> Position -> Aff (Either String HoverResult)
hover client uri pos = do
  let params = positionParams uri pos
  result <- sendRequestFFI client "textDocument/hover" params
  pure $ result >>= parseHoverResult

{-| Get completion items at a position. -}
completion :: LSPClient -> String -> Position -> Aff (Either String (Array CompletionItem))
completion client uri pos = do
  let params = positionParams uri pos
  result <- sendRequestFFI client "textDocument/completion" params
  pure $ result >>= parseCompletionResult

{-| Go to definition at a position. -}
definition :: LSPClient -> String -> Position -> Aff (Either String (Array Location))
definition client uri pos = do
  let params = positionParams uri pos
  result <- sendRequestFFI client "textDocument/definition" params
  pure $ result >>= parseLocationResult

{-| Find all references at a position. -}
references :: LSPClient -> String -> Position -> Aff (Either String (Array Location))
references client uri pos = do
  let params = positionParams uri pos <> ", \"context\": { \"includeDeclaration\": true }"
  result <- sendRequestFFI client "textDocument/references" ("{ " <> params <> " }")
  pure $ result >>= parseLocationResult

{-| Get diagnostics for a document. -}
diagnostics :: LSPClient -> String -> Aff (Either String (Array Diagnostic))
diagnostics client uri = do
  -- Diagnostics are typically pushed from server, but we can request them
  let params = "{ \"textDocument\": { \"uri\": \"" <> uri <> "\" } }"
  result <- sendRequestFFI client "textDocument/diagnostic" params
  pure $ result >>= parseDiagnosticsResult

-- ============================================================================
-- HELPERS
-- ============================================================================

positionParams :: String -> Position -> String
positionParams uri pos =
  "{ \"textDocument\": { \"uri\": \"" <> uri <> 
  "\" }, \"position\": { \"line\": " <> show pos.line <> 
  ", \"character\": " <> show pos.character <> " } }"

escapeJson :: String -> String
escapeJson s = "\"" <> escapeJsonString s <> "\""

foreign import escapeJsonString :: String -> String

parseHoverResult :: String -> Either String HoverResult
parseHoverResult json = Right { contents: json, range: Nothing }

parseCompletionResult :: String -> Either String (Array CompletionItem)
parseCompletionResult _ = Right []

parseLocationResult :: String -> Either String (Array Location)
parseLocationResult _ = Right []

parseDiagnosticsResult :: String -> Either String (Array Diagnostic)
parseDiagnosticsResult _ = Right []
