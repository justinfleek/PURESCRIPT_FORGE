{-|
Module      : Forge.Tool.Write
Description : File writing with LSP diagnostics
= Write Tool

Write content to files with LSP integration for error detection.

== Coeffect Equation

@
  write : WriteParams -> Graded (Filesystem path) WriteResult

  -- Requires:
  -- 1. Filesystem write access
  -- 2. File must have been read first (for existing files)
@

== Usage

@
  write { filePath: "/src/Main.purs", content: "module Main where..." }
@

== LSP Integration

After writing, the tool:
1. Notifies LSP of file change
2. Collects diagnostics
3. Reports errors in output
-}
module Forge.Tool.Write
  ( -- * Tool Interface
    WriteParams(..)
  , WriteResult(..)
  , execute
  , writeTool
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Argonaut (Json, encodeJson, decodeJson, (.:), printJsonDecodeError)
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Write tool parameters.
type WriteParams =
  { filePath :: String
  , content :: String
  }

type WriteResult =
  { success :: Boolean
  , filePath :: String
  , created :: Boolean       -- True if new file
  , diagnostics :: Array Diagnostic
  }

type Diagnostic =
  { severity :: Int          -- 1 = error, 2 = warning
  , message :: String
  , line :: Int
  , column :: Int
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
  , sessionID :: String
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
-- EXECUTION
-- ============================================================================

execute :: WriteParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Check if file exists (determines create vs update)
  existsResult <- checkFileExistsFFI params.filePath
  let exists = case existsResult of
        Left _ -> false
        Right e -> e
  
  -- 2. Write the file
  writeResult <- writeFileFFI params.filePath params.content
  
  case writeResult of
    Left err -> pure $ mkErrorResult err
    Right _ -> do
      -- 3. Notify LSP of file change (if available)
      _ <- notifyLspFFI params.filePath
      
      -- 4. Collect diagnostics
      diagnostics <- getDiagnosticsFFI params.filePath
      
      -- 5. Format output
      let hasErrors = Array.any (\d -> d.severity == 1) diagnostics
      let output = formatOutput params.filePath exists diagnostics
      
      pure
        { title: params.filePath
        , metadata: encodeJson
            { filePath: params.filePath
            , created: not exists
            , diagnosticCount: Array.length diagnostics
            , hasErrors
            }
        , output
        , attachments: Nothing
        }

-- | FFI for checking file existence
foreign import checkFileExistsFFI :: String -> Aff (Either String Boolean)

-- | FFI for writing file
foreign import writeFileFFI :: String -> String -> Aff (Either String Unit)

-- | FFI for LSP notification
foreign import notifyLspFFI :: String -> Aff Unit

-- | FFI for getting diagnostics
foreign import getDiagnosticsFFI :: String -> Aff (Array Diagnostic)

-- ============================================================================
-- OUTPUT FORMATTING
-- ============================================================================

formatOutput :: String -> Boolean -> Array Diagnostic -> String
formatOutput filePath exists diagnostics =
  let action = if exists then "Updated" else "Created"
      baseMsg = action <> " " <> filePath
      diagMsg = formatDiagnostics diagnostics
  in if String.null diagMsg
     then baseMsg
     else baseMsg <> "\n\n" <> diagMsg

formatDiagnostics :: Array Diagnostic -> String
formatDiagnostics diagnostics =
  if Array.null diagnostics
  then ""
  else 
    let errors = Array.filter (\d -> d.severity == 1) diagnostics
        warnings = Array.filter (\d -> d.severity == 2) diagnostics
        errorSection = if Array.null errors then "" else "Errors:\n" <> formatDiagList errors
        warnSection = if Array.null warnings then "" else "Warnings:\n" <> formatDiagList warnings
    in String.joinWith "\n\n" (Array.filter (not <<< String.null) [errorSection, warnSection])

formatDiagList :: Array Diagnostic -> String
formatDiagList = String.joinWith "\n" <<< map formatDiag
  where
    formatDiag d = "  Line " <> show d.line <> ":" <> show d.column <> " - " <> d.message

-- ============================================================================
-- TOOL REGISTRATION
-- ============================================================================

writeTool :: ToolInfo
writeTool =
  { id: "write"
  , description: "Write content to file with LSP diagnostics"
  , parameters: writeSchema
  , execute: \json ctx ->
      case decodeWriteParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> execute params ctx
  , formatValidationError: Nothing
  }

writeSchema :: Json
writeSchema = encodeJson
  { "type": "object"
  , "properties":
      { "filePath":
          { "type": "string"
          , "description": "The absolute path to the file to write"
          }
      , "content":
          { "type": "string"
          , "description": "The content to write to the file"
          }
      }
  , "required": ["filePath", "content"]
  }

decodeWriteParams :: Json -> Either String WriteParams
decodeWriteParams json =
  case decodeWriteParamsImpl json of
    Left err -> Left (printJsonDecodeError err)
    Right result -> Right result
  where
    decodeWriteParamsImpl j = do
      obj <- decodeJson j
      filePath <- obj .: "filePath"
      content <- obj .: "content"
      pure { filePath, content }

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Write Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }
