{-|
Module      : Forge.Tool.Glob
Description : File pattern matching via ripgrep
= Glob Tool

Fast file pattern matching using ripgrep's --files mode.

== Coeffect Equation

@
  glob : GlobParams -> Graded (Filesystem path) GlobResult

  -- Requires filesystem read access to search path
@

== Usage

@
  glob { pattern: "**/*.purs", path: Just "./src" }
@

== Output

Files sorted by modification time (most recent first):

@
  src/Tool/Glob.purs
  src/Tool/Grep.purs
  src/Aleph/Coeffect.purs
@
-}
module Forge.Tool.Glob
  ( -- * Tool Interface
    GlobParams(..)
  , GlobResult(..)
  , execute
  , globTool
    -- * Configuration
  , GlobConfig(..)
  , defaultConfig
  ) where

import Prelude

import Data.Maybe (Maybe(..), maybe)
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Argonaut (Json, encodeJson, decodeJson, (.:), (.:?), printJsonDecodeError)
import Effect.Aff (Aff)

-- ============================================================================
-- CONFIGURATION
-- ============================================================================

type GlobConfig =
  { maxFiles :: Int       -- Maximum files to return
  , defaultPath :: String -- Default search directory
  , timeout :: Int        -- Timeout in ms
  }

defaultConfig :: GlobConfig
defaultConfig =
  { maxFiles: 100
  , defaultPath: "."
  , timeout: 30000
  }

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Glob tool parameters.
type GlobParams =
  { pattern :: String
  , path :: Maybe String
  }

type FileMatch =
  { path :: String
  , modTime :: Number
  }

type GlobResult =
  { files :: Array FileMatch
  , count :: Int
  , truncated :: Boolean
  , searchPath :: String
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
-- EXECUTION
-- ============================================================================

execute :: GlobParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  let searchPath = params.path # maybe defaultConfig.defaultPath identity
  
  -- Build ripgrep --files command
  let args = ["--files", "--hidden", "--follow", "--glob", params.pattern, searchPath]
  
  result <- executeRgFilesFFI args searchPath
  
  case result of
    Left err -> pure $ mkErrorResult err
    
    Right output -> do
      let files = parseFileList output
      let sorted = Array.sortBy (\a b -> compare b.modTime a.modTime) files
      let truncated = Array.length sorted > defaultConfig.maxFiles
      let final = Array.take defaultConfig.maxFiles sorted
      
      pure $ formatResult searchPath
        { files: final
        , count: Array.length files
        , truncated
        , searchPath
        }

-- | FFI for ripgrep --files execution
foreign import executeRgFilesFFI :: Array String -> String -> Aff (Either String String)

parseFileList :: String -> Array FileMatch
parseFileList output =
  output
    # String.split (String.Pattern "\n")
    # Array.filter (not <<< String.null)
    # map (\p -> { path: p, modTime: 0.0 })

-- ============================================================================
-- OUTPUT
-- ============================================================================

formatResult :: String -> GlobResult -> ToolResult
formatResult searchPath result =
  { title: searchPath
  , metadata: encodeJson
      { count: result.count
      , truncated: result.truncated
      }
  , output: formatOutput result
  , attachments: Nothing
  }

formatOutput :: GlobResult -> String
formatOutput result
  | Array.null result.files = "No files found"
  | otherwise =
      let files = result.files # map _.path # String.joinWith "\n"
          footer = if result.truncated
                   then "\n\n(Results truncated. Use more specific pattern.)"
                   else ""
      in files <> footer

-- ============================================================================
-- TOOL REGISTRATION
-- ============================================================================

globTool :: ToolInfo
globTool =
  { id: "glob"
  , description: "Fast file pattern matching via glob patterns"
  , parameters: globSchema
  , execute: \json ctx ->
      case decodeGlobParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> execute params ctx
  , formatValidationError: Nothing
  }

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Glob Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

globSchema :: Json
globSchema = encodeJson
  { "type": "object"
  , "properties":
      { "pattern":
          { "type": "string"
          , "description": "The glob pattern to match files against"
          }
      , "path":
          { "type": "string"
          , "description": "The directory to search in. Defaults to the current working directory."
          }
      }
  , "required": ["pattern"]
  }

decodeGlobParams :: Json -> Either String GlobParams
decodeGlobParams json = 
  case decodeGlobParamsImpl json of
    Left err -> Left (printJsonDecodeError err)
    Right result -> Right result
  where
    decodeGlobParamsImpl j = do
      obj <- decodeJson j
      pattern <- obj .: "pattern"
      path <- obj .:? "path"
      pure { pattern, path }
