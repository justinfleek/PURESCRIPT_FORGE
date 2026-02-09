{-|
Module      : Forge.LSP.Index
Description : LSP Main Entry Point

High-level LSP interface that manages multiple language servers
and provides a unified API for language features.

== Supported Languages

Language servers are auto-detected based on file extensions and
project configuration.

| Language   | Server            | Extensions       |
|------------|-------------------|------------------|
| TypeScript | typescript-language-server | .ts, .tsx |
| JavaScript | typescript-language-server | .js, .jsx |
| Rust       | rust-analyzer     | .rs              |
| Go         | gopls             | .go              |
| Python     | pyright           | .py              |
| Haskell    | haskell-language-server | .hs       |
| PureScript | purescript-language-server | .purs   |
-}
module Forge.LSP.Index
  ( -- * Initialization
    init
  , shutdown
  , isInitialized
    -- * Document Operations
  , openFile
  , closeFile
  , getFileLanguage
    -- * LSP Features
  , getDiagnostics
  , getHover
  , getCompletions
  , getDefinition
  , getReferences
    -- * Server Management
  , getActiveServers
  , restartServer
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)
import Forge.LSP.Client as Client
import Forge.LSP.Server as Server

-- ============================================================================
-- TYPES
-- ============================================================================

type LSPState =
  { initialized :: Boolean
  , workspaceRoot :: String
  , clients :: Array Client.LSPClient
  }

-- | Diagnostic with file path
type FileDiagnostic =
  { file :: String
  , line :: Int
  , column :: Int
  , severity :: String
  , message :: String
  }

-- | Hover information
type HoverInfo =
  { content :: String
  , language :: Maybe String
  }

-- | Completion suggestion
type CompletionSuggestion =
  { label :: String
  , kind :: String
  , detail :: Maybe String
  , insertText :: String
  }

-- | Definition location
type DefinitionLocation =
  { file :: String
  , line :: Int
  , column :: Int
  }

-- ============================================================================
-- FFI
-- ============================================================================

foreign import getStateFFI :: Aff (Maybe LSPState)
foreign import setStateFFI :: LSPState -> Aff Unit
foreign import getServerCommandFFI :: String -> Aff (Maybe { command :: String, args :: Array String })

-- ============================================================================
-- INITIALIZATION
-- ============================================================================

{-| Initialize LSP for a workspace.

Detects project languages and starts appropriate language servers.
-}
init :: String -> Aff (Either String Unit)
init workspaceRoot = do
  -- Check if already initialized
  existing <- getStateFFI
  case existing of
    Just state | state.initialized && state.workspaceRoot == workspaceRoot ->
      pure $ Right unit
    _ -> do
      -- Create initial state
      let state = 
            { initialized: true
            , workspaceRoot
            , clients: []
            }
      setStateFFI state
      pure $ Right unit

{-| Shutdown all LSP servers. -}
shutdown :: Aff (Either String Unit)
shutdown = do
  state <- getStateFFI
  case state of
    Nothing -> pure $ Right unit
    Just s -> do
      -- Disconnect all clients
      _ <- traverse (\c -> Client.disconnect c) s.clients
      setStateFFI s { initialized = false, clients = [] }
      pure $ Right unit

{-| Check if LSP is initialized. -}
isInitialized :: Aff Boolean
isInitialized = do
  state <- getStateFFI
  pure $ case state of
    Just s -> s.initialized
    Nothing -> false

-- ============================================================================
-- DOCUMENT OPERATIONS
-- ============================================================================

{-| Open a file for LSP features. -}
openFile :: String -> Aff (Either String Unit)
openFile filePath = do
  state <- getStateFFI
  case state of
    Nothing -> pure $ Left "LSP not initialized"
    Just s -> do
      let lang = getFileLanguage filePath
      -- Find or create client for this language
      client <- getOrCreateClient s.workspaceRoot lang
      case client of
        Left err -> pure $ Left err
        Right c -> do
          content <- readFileFFI filePath
          case content of
            Left err -> pure $ Left err
            Right text -> 
              Client.openDocument c ("file://" <> filePath) lang text

{-| Close a file. -}
closeFile :: String -> Aff (Either String Unit)
closeFile filePath = do
  state <- getStateFFI
  case state of
    Nothing -> pure $ Right unit
    Just s -> do
      let lang = getFileLanguage filePath
      case Array.find (\c -> c.config.language == lang) s.clients of
        Nothing -> pure $ Right unit
        Just client -> Client.closeDocument client ("file://" <> filePath)

{-| Get the language ID for a file based on extension. -}
getFileLanguage :: String -> String
getFileLanguage path =
  let ext = getExtension path
  in case ext of
    ".ts" -> "typescript"
    ".tsx" -> "typescriptreact"
    ".js" -> "javascript"
    ".jsx" -> "javascriptreact"
    ".rs" -> "rust"
    ".go" -> "go"
    ".py" -> "python"
    ".hs" -> "haskell"
    ".purs" -> "purescript"
    ".json" -> "json"
    ".md" -> "markdown"
    ".html" -> "html"
    ".css" -> "css"
    _ -> "plaintext"

-- ============================================================================
-- LSP FEATURES
-- ============================================================================

{-| Get diagnostics for a file. -}
getDiagnostics :: String -> Aff (Either String (Array FileDiagnostic))
getDiagnostics filePath = do
  state <- getStateFFI
  case state of
    Nothing -> pure $ Left "LSP not initialized"
    Just s -> do
      let lang = getFileLanguage filePath
      case Array.find (\c -> c.config.language == lang) s.clients of
        Nothing -> pure $ Right []
        Just client -> do
          result <- Client.diagnostics client ("file://" <> filePath)
          pure $ result >>= \diags ->
            Right $ map (\d -> 
              { file: filePath
              , line: d.range.start.line
              , column: d.range.start.character
              , severity: severityToString d.severity
              , message: d.message
              }) diags

{-| Get hover information at a position. -}
getHover :: String -> Int -> Int -> Aff (Either String HoverInfo)
getHover filePath line column = do
  state <- getStateFFI
  case state of
    Nothing -> pure $ Left "LSP not initialized"
    Just s -> do
      let lang = getFileLanguage filePath
      case Array.find (\c -> c.config.language == lang) s.clients of
        Nothing -> pure $ Left "No language server for this file type"
        Just client -> do
          result <- Client.hover client ("file://" <> filePath) { line, character: column }
          pure $ result >>= \h -> Right { content: h.contents, language: Just lang }

{-| Get completions at a position. -}
getCompletions :: String -> Int -> Int -> Aff (Either String (Array CompletionSuggestion))
getCompletions filePath line column = do
  state <- getStateFFI
  case state of
    Nothing -> pure $ Left "LSP not initialized"
    Just s -> do
      let lang = getFileLanguage filePath
      case Array.find (\c -> c.config.language == lang) s.clients of
        Nothing -> pure $ Right []
        Just client -> do
          result <- Client.completion client ("file://" <> filePath) { line, character: column }
          pure $ result >>= \items ->
            Right $ map (\i -> 
              { label: i.label
              , kind: completionKindToString i.kind
              , detail: i.detail
              , insertText: case i.insertText of
                  Just t -> t
                  Nothing -> i.label
              }) items

{-| Go to definition. -}
getDefinition :: String -> Int -> Int -> Aff (Either String (Array DefinitionLocation))
getDefinition filePath line column = do
  state <- getStateFFI
  case state of
    Nothing -> pure $ Left "LSP not initialized"
    Just s -> do
      let lang = getFileLanguage filePath
      case Array.find (\c -> c.config.language == lang) s.clients of
        Nothing -> pure $ Right []
        Just client -> do
          result <- Client.definition client ("file://" <> filePath) { line, character: column }
          pure $ result >>= \locs ->
            Right $ map (\l -> 
              { file: String.drop 7 l.uri  -- Remove "file://" prefix
              , line: l.range.start.line
              , column: l.range.start.character
              }) locs

{-| Find references. -}
getReferences :: String -> Int -> Int -> Aff (Either String (Array DefinitionLocation))
getReferences filePath line column = do
  state <- getStateFFI
  case state of
    Nothing -> pure $ Left "LSP not initialized"
    Just s -> do
      let lang = getFileLanguage filePath
      case Array.find (\c -> c.config.language == lang) s.clients of
        Nothing -> pure $ Right []
        Just client -> do
          result <- Client.references client ("file://" <> filePath) { line, character: column }
          pure $ result >>= \locs ->
            Right $ map (\l -> 
              { file: String.drop 7 l.uri
              , line: l.range.start.line
              , column: l.range.start.character
              }) locs

-- ============================================================================
-- SERVER MANAGEMENT
-- ============================================================================

{-| Get list of active language servers. -}
getActiveServers :: Aff (Array String)
getActiveServers = do
  state <- getStateFFI
  case state of
    Nothing -> pure []
    Just s -> pure $ map (\c -> c.config.language) $ 
              Array.filter Client.isConnected s.clients

{-| Restart a language server. -}
restartServer :: String -> Aff (Either String Unit)
restartServer language = do
  state <- getStateFFI
  case state of
    Nothing -> pure $ Left "LSP not initialized"
    Just s -> do
      case Array.find (\c -> c.config.language == language) s.clients of
        Nothing -> pure $ Left ("No server for language: " <> language)
        Just client -> do
          _ <- Client.disconnect client
          _ <- Client.connect client
          pure $ Right unit

-- ============================================================================
-- HELPERS
-- ============================================================================

getExtension :: String -> String
getExtension path =
  let parts = String.split (String.Pattern ".") path
  in case Array.last parts of
    Just ext -> "." <> ext
    Nothing -> ""

severityToString :: Int -> String
severityToString 1 = "error"
severityToString 2 = "warning"
severityToString 3 = "info"
severityToString 4 = "hint"
severityToString _ = "unknown"

completionKindToString :: Int -> String
completionKindToString 1 = "text"
completionKindToString 2 = "method"
completionKindToString 3 = "function"
completionKindToString 4 = "constructor"
completionKindToString 5 = "field"
completionKindToString 6 = "variable"
completionKindToString 7 = "class"
completionKindToString 8 = "interface"
completionKindToString 9 = "module"
completionKindToString _ = "unknown"

getOrCreateClient :: String -> String -> Aff (Either String Client.LSPClient)
getOrCreateClient workspaceRoot language = do
  serverCmd <- getServerCommandFFI language
  case serverCmd of
    Nothing -> pure $ Left ("No server configured for: " <> language)
    Just { command, args } -> do
      let config = 
            { serverCommand: command
            , serverArgs: args
            , workspaceRoot
            , language
            , initializationOptions: Nothing
            }
      Client.create config >>= case _ of
        Left err -> pure $ Left err
        Right client -> Client.connect client

foreign import readFileFFI :: String -> Aff (Either String String)
foreign import traverse :: forall a b. (a -> Aff b) -> Array a -> Aff (Array b)
