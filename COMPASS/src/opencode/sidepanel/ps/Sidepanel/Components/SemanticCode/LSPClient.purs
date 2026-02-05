{-|
Module      : Sidepanel.Components.SemanticCode.LSPClient
Description : Language Server Protocol client for semantic code understanding

LSP client for symbol navigation, go-to-definition, find references, etc.
-}
module Sidepanel.Components.SemanticCode.LSPClient where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes (Position)

-- | LSP client connection
type LSPConnection =
  { serverUri :: String
  , language :: String
  , isConnected :: Boolean
  , capabilities :: LSPCapabilities
  , connection :: LSPConnectionHandle  -- Internal connection handle
  }

-- | Opaque connection handle (managed by FFI)
foreign import data LSPConnectionHandle :: Type

-- | LSP server capabilities
type LSPServerCapabilities =
  { hover :: Boolean
  , definition :: Boolean
  , references :: Boolean
  , completion :: Boolean
  , signatureHelp :: Boolean
  , documentSymbol :: Boolean
  }

-- | LSP capabilities (alias for compatibility)
type LSPCapabilities = LSPServerCapabilities

-- | Symbol information
type SymbolInfo =
  { name :: String
  , kind :: SymbolKind
  , definition :: Location
  , type_ :: Maybe String
  , documentation :: Maybe String
  , containerName :: Maybe String
  }

-- | Symbol kind
data SymbolKind
  = File
  | Module
  | Namespace
  | Package
  | Class
  | Method
  | Property
  | Field
  | Constructor
  | Enum
  | Interface
  | Function
  | Variable
  | Constant
  | String
  | Number
  | Boolean
  | Array
  | Object
  | Key
  | Null
  | EnumMember
  | Struct
  | Event
  | Operator
  | TypeParameter

derive instance eqSymbolKind :: Eq SymbolKind

-- | Location in code
type Location =
  { uri :: String
  , range :: Range
  }

-- | Range in document
type Range =
  { start :: Position
  , end :: Position
  }

-- | Connect to LSP server
connectLSP :: String -> String -> Aff (Either String LSPConnection)
connectLSP language serverConfig = do
  -- Establish connection to LSP server via FFI
  -- serverConfig can be a JSON string with { command, args, rootUri } or a command string
  result <- connectLSPFFI language serverConfig
  case result of
    Left err -> pure $ Left err
    Right connectionData -> pure $ Right
      { serverUri: serverConfig
      , language: language
      , isConnected: connectionData.isConnected
      , capabilities: connectionData.capabilities
      , connection: connectionData.connection
      }

foreign import connectLSPFFI :: String -> String -> Aff (Either String { isConnected :: Boolean, capabilities :: LSPServerCapabilities, connection :: LSPConnectionHandle })

-- | Get symbol at position (hover)
getSymbolAtPosition :: LSPConnection -> String -> Position -> Aff (Maybe SymbolInfo)
getSymbolAtPosition connection fileUri position = do
  -- Call LSP textDocument/hover via FFI
  result <- hoverLSPFFI connection.connection fileUri position
  case result of
    Nothing -> pure Nothing
    Just info -> pure $ Just
      { name: info.name
      , kind: Function  -- Default, would parse from LSP response
      , definition: { uri: fileUri, range: info.range }
      , type_: info.type_
      , documentation: info.documentation
      , containerName: Nothing
      }

foreign import hoverLSPFFI :: LSPConnectionHandle -> String -> Position -> Aff (Maybe { name :: String, type_ :: Maybe String, documentation :: Maybe String, range :: Range })

-- | Notify LSP server that document was opened
notifyDocumentDidOpen :: LSPConnection -> String -> String -> String -> Aff Unit
notifyDocumentDidOpen connection fileUri languageId content = do
  notifyDocumentDidOpenFFI connection.connection fileUri languageId content
  pure unit

foreign import notifyDocumentDidOpenFFI :: LSPConnectionHandle -> String -> String -> String -> Aff Unit

-- | Notify LSP server that document was changed
notifyDocumentDidChange :: LSPConnection -> String -> String -> Aff Unit
notifyDocumentDidChange connection fileUri content = do
  notifyDocumentDidChangeFFI connection.connection fileUri content
  pure unit

foreign import notifyDocumentDidChangeFFI :: LSPConnectionHandle -> String -> String -> Aff Unit

-- | Notify LSP server that document was closed
notifyDocumentDidClose :: LSPConnection -> String -> Aff Unit
notifyDocumentDidClose connection fileUri = do
  notifyDocumentDidCloseFFI connection.connection fileUri
  pure unit

foreign import notifyDocumentDidCloseFFI :: LSPConnectionHandle -> String -> Aff Unit

-- | Disconnect from LSP server
disconnectLSP :: LSPConnection -> Aff Unit
disconnectLSP connection = do
  disconnectLSPFFI connection.connection
  pure unit

foreign import disconnectLSPFFI :: LSPConnectionHandle -> Aff Unit

-- | Go to definition
goToDefinition :: LSPConnection -> String -> Position -> Aff (Maybe Location)
goToDefinition connection fileUri position = do
  -- Call LSP textDocument/definition via FFI
  result <- definitionLSPFFI connection.connection fileUri position
  pure result

foreign import definitionLSPFFI :: LSPConnectionHandle -> String -> Position -> Aff (Maybe Location)

-- | Find all references
findReferences :: LSPConnection -> String -> Position -> Aff (Array Location)
findReferences connection fileUri position = do
  -- Call LSP textDocument/references via FFI
  result <- referencesLSPFFI connection.connection fileUri position
  pure result

foreign import referencesLSPFFI :: LSPConnectionHandle -> String -> Position -> Aff (Array Location)

-- | Get document symbols
getDocumentSymbols :: LSPConnection -> String -> Aff (Array SymbolInfo)
getDocumentSymbols connection fileUri = do
  -- Call LSP textDocument/documentSymbol via FFI
  result <- documentSymbolsLSPFFI connection.connection fileUri
  pure result

foreign import documentSymbolsLSPFFI :: LSPConnectionHandle -> String -> Aff (Array SymbolInfo)

-- | Get signature help
getSignatureHelp :: LSPConnection -> String -> Position -> Aff (Maybe SignatureHelp)
getSignatureHelp connection fileUri position = do
  -- Call LSP textDocument/signatureHelp via FFI
  result <- signatureHelpLSPFFI connection.connection fileUri position
  pure result

foreign import signatureHelpLSPFFI :: LSPConnectionHandle -> String -> Position -> Aff (Maybe SignatureHelp)

-- | Signature help information
type SignatureHelp =
  { signatures :: Array SignatureInformation
  , activeSignature :: Int
  , activeParameter :: Int
  }

-- | Signature information
type SignatureInformation =
  { label :: String
  , documentation :: Maybe String
  , parameters :: Array ParameterInformation
  }

-- | Parameter information
type ParameterInformation =
  { label :: String
  , documentation :: Maybe String
  }
