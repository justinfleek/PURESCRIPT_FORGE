{-|
Module      : Forge.Tool.Lsp
Description : Language Server Protocol integration tool
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
module Forge.Tool.Lsp
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
import Data.String as String
import Data.String.Pattern (Pattern(..))
import Data.Argonaut (Json, class EncodeJson, encodeJson, class DecodeJson, decodeJson, (.:), printJsonDecodeError)
import Data.Argonaut.Core as Json
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)

import Forge.LSP.Language (detectLanguage)

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

derive instance eqLspOperation :: Eq LspOperation

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

parseOperation :: String -> Maybe LspOperation
parseOperation s = case s of
  "goToDefinition" -> Just GoToDefinition
  "findReferences" -> Just FindReferences
  "hover" -> Just Hover
  "documentSymbol" -> Just DocumentSymbol
  "workspaceSymbol" -> Just WorkspaceSymbol
  "goToImplementation" -> Just GoToImplementation
  "prepareCallHierarchy" -> Just PrepareCallHierarchy
  "incomingCalls" -> Just IncomingCalls
  "outgoingCalls" -> Just OutgoingCalls
  _ -> Nothing

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

-- | Tool result type
type ToolResult =
  { title :: String
  , output :: String
  , metadata :: Json
  , attachments :: Maybe (Array Json)
  }

-- | Tool context
type ToolContext = 
  { workspaceRoot :: String
  }

-- | Tool info
type ToolInfo =
  { id :: String
  , description :: String
  , parameters :: Json
  , execute :: Json -> ToolContext -> Aff ToolResult
  , formatValidationError :: Maybe (Json -> String)
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
  fileExists <- checkFileExists filePath
  if not fileExists then
    pure $ mkErrorResult ("File not found: " <> filePath)
  else do
    -- 3. Check if LSP server available based on file extension
    lspAvailable <- checkLspAvailability filePath
    
    if not lspAvailable then
      pure $ mkErrorResult ("LSP server not available for file: " <> filePath)
    else do
      -- 4. Convert to 0-based position (LSP uses 0-based)
      let position = { line: params.line - 1, character: params.character - 1 }
      
      -- 5. Execute LSP operation
      lspResult <- callLspServer params.operation filePath position
      
      -- 6. Format output
      let output = formatLspResults params.operation lspResult
      
      pure
        { title: params.operation <> " " <> filePath <> ":" <> show params.line <> ":" <> show params.character
        , metadata: encodeJson 
            { operation: params.operation
            , filePath
            , position: { line: params.line, character: params.character }
            , resultCount: Array.length lspResult
            }
        , output
        , attachments: Nothing
        }

-- | Check if file exists
checkFileExists :: String -> Aff Boolean
checkFileExists filePath = do
  result <- fileExistsFFI filePath
  pure result

-- | FFI for file existence check
foreign import fileExistsFFI :: String -> Aff Boolean

-- | Check if LSP server is available for file type
-- | Determines availability based on file extension
checkLspAvailability :: String -> Aff Boolean
checkLspAvailability filePath = do
  pure $ case detectLanguage filePath of
    Nothing -> false
    Just lang -> case lang.serverCommand of
      Nothing -> false
      Just _ -> true

-- | Call LSP server operation
-- | Uses FFI to communicate with LSP server
callLspServer :: String -> String -> { line :: Int, character :: Int } -> Aff (Array Json)
callLspServer operation filePath position = do
  result <- callLspOperationFFI operation filePath position
  case result of
    Left _err -> pure []
    Right results -> pure results

-- | FFI for LSP operation calls
foreign import callLspOperationFFI :: String -> String -> { line :: Int, character :: Int } -> Aff (Either String (Array Json))

-- | Format LSP results for output
formatLspResults :: String -> Array Json -> String
formatLspResults operation results =
  if Array.null results
  then "No results found for " <> operation
  else operation <> " found " <> show (Array.length results) <> " result(s):\n\n" <>
       String.joinWith "\n" (Array.mapWithIndex formatResult results)
  where
    formatResult idx result =
      show (idx + 1) <> ". " <> Json.stringify result

{-| Tool registration. -}
lspTool :: ToolInfo
lspTool =
  { id: "lsp"
  , description: lspDescription
  , parameters: lspSchema
  , execute: \json ctx ->
      case decodeLspParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> execute params ctx
  , formatValidationError: Just formatValidationErrorImpl
  }

-- ============================================================================
-- HELPERS
-- ============================================================================

lspDescription :: String
lspDescription =
  "Perform Language Server Protocol operations for code intelligence. " <>
  "Use this for go-to-definition, find-references, hover documentation, " <>
  "and symbol lookup."

lspSchema :: Json
lspSchema = encodeJson
  { "type": "object"
  , properties:
      { operation: 
          { "type": "string"
          , enum: ["goToDefinition", "findReferences", "hover", "documentSymbol", 
                   "workspaceSymbol", "goToImplementation", "prepareCallHierarchy", 
                   "incomingCalls", "outgoingCalls"]
          , description: "LSP operation to perform"
          }
      , filePath: { "type": "string", description: "Path to the file" }
      , line: { "type": "integer", description: "Line number (1-based)", minimum: 1 }
      , character: { "type": "integer", description: "Character position (1-based)", minimum: 1 }
      }
  , required: ["operation", "filePath", "line", "character"]
  }

decodeLspParams :: Json -> Either String LspParams
decodeLspParams json =
  case decodeLspParamsImpl json of
    Left err -> Left (printJsonDecodeError err)
    Right result -> Right result
  where
    decodeLspParamsImpl j = do
      obj <- decodeJson j
      operation <- obj .: "operation"
      filePath <- obj .: "filePath"
      line <- obj .: "line"
      character <- obj .: "character"
      pure { operation, filePath, line, character }

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "LSP Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatValidationErrorImpl :: Json -> String
formatValidationErrorImpl _ = "Invalid LSP parameters"
