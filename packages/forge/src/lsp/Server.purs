{-|
Module      : Forge.LSP.Server
Description : LSP Server Management

Manages Language Server Protocol server processes. Handles starting,
stopping, and monitoring language servers for different languages.

== Server Discovery

Servers are discovered in order:
1. Project-local configuration (.forge/lsp.json)
2. User configuration (~/.forge/lsp.json)
3. Built-in defaults for common languages
-}
module Forge.LSP.Server
  ( -- * Types
    LSPServer
  , ServerConfig
  , ServerStatus(..)
    -- * Server Operations
  , start
  , stop
  , restart
  , isRunning
    -- * Server Discovery
  , discover
  , getServerForLanguage
  , listAvailableServers
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Server status
data ServerStatus
  = Stopped
  | Starting
  | Running
  | Stopping
  | Failed String

derive instance eqServerStatus :: Eq ServerStatus

instance showServerStatus :: Show ServerStatus where
  show Stopped = "stopped"
  show Starting = "starting"
  show Running = "running"
  show Stopping = "stopping"
  show (Failed e) = "failed: " <> e

-- | Server configuration
type ServerConfig =
  { command :: String
  , args :: Array String
  , env :: Array { key :: String, value :: String }
  , initOptions :: Maybe String
  }

-- | LSP Server info
type LSPServer =
  { language :: String
  , config :: ServerConfig
  , status :: ServerStatus
  , processId :: Maybe Int
  , capabilities :: Array String
  }

-- | Language server definition
type ServerDefinition =
  { language :: String
  , command :: String
  , args :: Array String
  , filePatterns :: Array String
  }

-- ============================================================================
-- FFI
-- ============================================================================

foreign import startServerFFI :: String -> ServerConfig -> Aff (Either String LSPServer)
foreign import stopServerFFI :: String -> Aff (Either String Unit)
foreign import getServerStatusFFI :: String -> Aff (Maybe ServerStatus)
foreign import checkCommandExistsFFI :: String -> Aff Boolean

-- ============================================================================
-- SERVER OPERATIONS
-- ============================================================================

{-| Start an LSP server for a language.

If no server is configured for the language, attempts to discover one.
-}
start :: String -> Aff (Either String LSPServer)
start language = do
  -- Check if already running
  status <- getServerStatusFFI language
  case status of
    Just Running -> do
      -- Return existing server info
      pure $ Left "Server already running"
    _ -> do
      -- Get server config
      config <- getServerForLanguage language
      case config of
        Nothing -> pure $ Left ("No language server found for: " <> language)
        Just serverDef -> do
          let cfg = 
                { command: serverDef.command
                , args: serverDef.args
                , env: []
                , initOptions: Nothing
                }
          startServerFFI language cfg

{-| Stop an LSP server. -}
stop :: String -> Aff (Either String Unit)
stop = stopServerFFI

{-| Restart an LSP server. -}
restart :: String -> Aff (Either String LSPServer)
restart language = do
  _ <- stop language
  start language

{-| Check if a server is running. -}
isRunning :: String -> Aff Boolean
isRunning language = do
  status <- getServerStatusFFI language
  pure $ case status of
    Just Running -> true
    _ -> false

-- ============================================================================
-- SERVER DISCOVERY
-- ============================================================================

{-| Discover available language servers. -}
discover :: Aff (Array ServerDefinition)
discover = do
  -- Check which default servers are available
  available <- traverse checkServer defaultServers
  pure $ Array.catMaybes available
  where
    checkServer :: ServerDefinition -> Aff (Maybe ServerDefinition)
    checkServer def = do
      exists <- checkCommandExistsFFI def.command
      if exists
        then pure $ Just def
        else pure Nothing

{-| Get server configuration for a language. -}
getServerForLanguage :: String -> Aff (Maybe ServerDefinition)
getServerForLanguage language =
  pure $ Array.find (\s -> s.language == language) defaultServers

{-| List all known language servers. -}
listAvailableServers :: Aff (Array { language :: String, available :: Boolean })
listAvailableServers = do
  results <- traverse checkAvailable defaultServers
  pure results
  where
    checkAvailable :: ServerDefinition -> Aff { language :: String, available :: Boolean }
    checkAvailable def = do
      available <- checkCommandExistsFFI def.command
      pure { language: def.language, available }

-- ============================================================================
-- DEFAULT SERVERS
-- ============================================================================

defaultServers :: Array ServerDefinition
defaultServers =
  [ { language: "typescript"
    , command: "typescript-language-server"
    , args: ["--stdio"]
    , filePatterns: ["*.ts", "*.tsx"]
    }
  , { language: "javascript"
    , command: "typescript-language-server"
    , args: ["--stdio"]
    , filePatterns: ["*.js", "*.jsx"]
    }
  , { language: "rust"
    , command: "rust-analyzer"
    , args: []
    , filePatterns: ["*.rs"]
    }
  , { language: "go"
    , command: "gopls"
    , args: ["serve"]
    , filePatterns: ["*.go"]
    }
  , { language: "python"
    , command: "pyright-langserver"
    , args: ["--stdio"]
    , filePatterns: ["*.py"]
    }
  , { language: "haskell"
    , command: "haskell-language-server-wrapper"
    , args: ["--lsp"]
    , filePatterns: ["*.hs"]
    }
  , { language: "purescript"
    , command: "purescript-language-server"
    , args: ["--stdio"]
    , filePatterns: ["*.purs"]
    }
  , { language: "json"
    , command: "vscode-json-language-server"
    , args: ["--stdio"]
    , filePatterns: ["*.json"]
    }
  , { language: "html"
    , command: "vscode-html-language-server"
    , args: ["--stdio"]
    , filePatterns: ["*.html"]
    }
  , { language: "css"
    , command: "vscode-css-language-server"
    , args: ["--stdio"]
    , filePatterns: ["*.css", "*.scss"]
    }
  ]

-- ============================================================================
-- HELPERS
-- ============================================================================

traverse :: forall a b. (a -> Aff b) -> Array a -> Aff (Array b)
traverse f arr = traverseImpl f arr

foreign import traverseImpl :: forall a b. (a -> Aff b) -> Array a -> Aff (Array b)
