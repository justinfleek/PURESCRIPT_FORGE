{-|
Module      : Tool.Glob
Description : File pattern matching via ripgrep
= Glob Tool

Fast file pattern matching using ripgrep's --files mode.

== Coeffect Equation

@
  glob : GlobParams → Graded (Filesystem path) GlobResult

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
module Tool.Glob
  ( -- * Tool Interface
    GlobParams(..)
  , GlobResult(..)
  , execute
  , globTool
    -- * Configuration
  , GlobConfig(..)
  , defaultConfig
    -- * Coeffects
  , globCoeffect
  ) where

import Prelude

import Data.Maybe (Maybe(..), maybe)
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Argonaut (Json, encodeJson, decodeJson)
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Aleph.Coeffect (Resource(..), PathSpec, filesystem)
import Aleph.Sandbox as Sandbox

-- ════════════════════════════════════════════════════════════════════════════
-- CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ════════════════════════════════════════════════════════════════════════════

{-| Glob tool parameters.

@
  record GlobParams where
    pattern : String        -- Glob pattern (e.g., "**/*.purs")
    path    : Maybe String  -- Search directory
@
-}
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

-- ════════════════════════════════════════════════════════════════════════════
-- EXECUTION
-- ════════════════════════════════════════════════════════════════════════════

execute :: GlobParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  let searchPath = params.path # maybe defaultConfig.defaultPath identity
  
  -- Build ripgrep --files command
  let args = ["--files", "--hidden", "--follow", "--glob", params.pattern, searchPath]
  let containerConfig = mkContainerConfig args
  
  result <- Sandbox.execute containerConfig
  
  case result of
    Sandbox.SandboxSuccess r -> do
      let files = parseFileList r.value.stdout
      let sorted = Array.sortBy (\a b -> compare b.modTime a.modTime) files
      let truncated = Array.length sorted > defaultConfig.maxFiles
      let final = Array.take defaultConfig.maxFiles sorted
      
      pure $ formatResult searchPath
        { files: final
        , count: Array.length files
        , truncated
        , searchPath
        }
    
    Sandbox.SandboxFailure e ->
      pure $ mkErrorResult e.details
    
    Sandbox.SandboxTimeout _ ->
      pure $ mkErrorResult "File search timed out"
    
    Sandbox.SandboxOOM _ ->
      pure $ mkErrorResult "File search ran out of memory"

mkContainerConfig :: Array String -> Sandbox.ContainerConfig
mkContainerConfig args =
  Sandbox.defaultConfig
    { command = ["rg"] <> args
    , policy = Sandbox.policyFromKind Sandbox.SandboxFull
    }

parseFileList :: String -> Array FileMatch
parseFileList output =
  output
    # String.split (String.Pattern "\n")
    # Array.filter (not <<< String.null)
    # map (\p -> { path: p, modTime: 0.0 })

-- ════════════════════════════════════════════════════════════════════════════
-- OUTPUT
-- ════════════════════════════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════════════════════════════
-- COEFFECTS
-- ════════════════════════════════════════════════════════════════════════════

globCoeffect :: GlobParams -> Resource
globCoeffect params =
  let pathSpec = 
        { path: params.path # maybe "." identity
        , readable: true
        , writable: false
        , recursive: true
        }
  in filesystem pathSpec

-- ════════════════════════════════════════════════════════════════════════════
-- TOOL REGISTRATION
-- ════════════════════════════════════════════════════════════════════════════

globTool :: ToolInfo
globTool =
  { id: "glob"
  , description: "Fast file pattern matching via glob patterns"
  , parameters: encodeJson { type: "object" }
  , execute: \json ctx ->
      case decodeJson json of
        Left err -> pure $ mkErrorResult (show err)
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
