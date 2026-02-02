{-|
Module      : Tool.Lsp
Description : Language Server Protocol integration tool
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= LSP Tool

Provides access to Language Server Protocol operations for code
intelligence features like go-to-definition, find references, and
symbol lookup.

== Coeffect Equation

@
  lsp : LspParams -> Graded (Filesystem path * LSP) ToolResult

  -- Requires:
  -- 1. Filesystem access to the target file
  -- 2. LSP server connection for the file type
@

== Supported Operations

| Operation           | Description                          |
|---------------------|--------------------------------------|
| goToDefinition      | Jump to symbol definition            |
| findReferences      | Find all references to symbol        |
| hover               | Get hover documentation              |
| documentSymbol      | List symbols in document             |
| workspaceSymbol     | Search symbols across workspace      |
| goToImplementation  | Jump to implementation               |
| prepareCallHierarchy| Get call hierarchy item              |
| incomingCalls       | Get callers of a function            |
| outgoingCalls       | Get functions called                 |

== Position Format

Positions are 1-based (as shown in editors):
@
  file.ts:42:10  -- Line 42, column 10
@
-}
module Tool.Lsp
  ( -- * Tool Interface
    LspParams(..)
  , execute
  , lspTool
    -- * Operations
  , LspOperation(..)
  , Position(..)
    -- * Response Types
  , Location(..)
  , SymbolInfo(..)
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.Argonaut (Json, class EncodeJson, encodeJson, decodeJson)
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Aleph.Coeffect (Resource(..))

-- ============================================================================
-- TYPES
-- ============================================================================

{-| LSP operation type. -}
data LspOperation
  = GoToDefinition
  | FindReferences
  | Hover
  | DocumentSymbol
  | WorkspaceSymbol
  | GoToImplementation
  | PrepareCallHierarchy
  | IncomingCalls
  | OutgoingCalls

instance showLspOperation :: Show LspOperation where
  show GoToDefinition = "goToDefinition"
  show FindReferences = "findReferences"
  show Hover = "hover"
  show DocumentSymbol = "documentSymbol"
  show WorkspaceSymbol = "workspaceSymbol"
  show GoToImplementation = "goToImplementation"
  show PrepareCallHierarchy = "prepareCallHierarchy"
  show IncomingCalls = "incomingCalls"
  show OutgoingCalls = "outgoingCalls"

{-| Source position (1-based). -}
type Position =
  { line :: Int      -- 1-based line number
  , character :: Int -- 1-based column number
  }

{-| Parameters for LSP tool.

@
  record LspParams where
    operation : LspOperation
    filePath  : String
    line      : Int
    character : Int
@
-}
type LspParams =
  { operation :: String
  , filePath :: String
  , line :: Int
  , character :: Int
  }

{-| Location result from LSP. -}
type Location =
  { uri :: String
  , line :: Int
  , character :: Int
  }

{-| Symbol information from LSP. -}
type SymbolInfo =
  { name :: String
  , kind :: String
  , location :: Location
  }

-- ============================================================================
-- TOOL INTERFACE
-- ============================================================================

{-| Execute LSP tool.

Performs the specified LSP operation and returns results.
-}
execute :: LspParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Resolve file path
  let filePath = params.filePath
  
  -- 2. Check if file exists
  -- TODO: File existence check
  
  -- 3. Check if LSP server available
  -- TODO: LSP availability check
  
  -- 4. Convert to 0-based position
  let position = { line: params.line - 1, character: params.character - 1 }
  
  -- 5. Execute LSP operation
  -- TODO: Call LSP server
  let results = [] :: Array Json
  
  -- 6. Format output
  let output = if Array.null results
        then "No results found for " <> params.operation
        else "TODO: Format LSP results"
  
  pure
    { title: params.operation <> " " <> filePath <> ":" <> show params.line <> ":" <> show params.character
    , metadata: encodeJson { results }
    , output
    , attachments: Nothing
    }

{-| Tool registration. -}
lspTool :: ToolInfo
lspTool =
  { id: "lsp"
  , description: lspDescription
  , parameters: encodeJson lspSchema
  , execute: \json ctx ->
      case decodeLspParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> execute params ctx
  , formatValidationError: Just formatValidationError
  }

-- ============================================================================
-- HELPERS
-- ============================================================================

lspDescription :: String
lspDescription =
  "Perform Language Server Protocol operations for code intelligence. " <>
  "Use this for go-to-definition, find-references, hover documentation, " <>
  "and symbol lookup."

lspSchema :: { type :: String }
lspSchema = { type: "object" }

decodeLspParams :: Json -> Either String LspParams
decodeLspParams _ = notImplemented "decodeLspParams"

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "LSP Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatValidationError :: Json -> String
formatValidationError _ = "Invalid LSP parameters"

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
