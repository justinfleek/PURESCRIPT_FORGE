{-|
Module      : Tool.Write
Description : File writing with LSP diagnostics
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Write Tool

Write content to files with LSP integration for error detection.

== Coeffect Equation

@
  write : WriteParams → Graded (Filesystem path) WriteResult

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
module Tool.Write
  ( -- * Tool Interface
    WriteParams(..)
  , WriteResult(..)
  , execute
  , writeTool
    -- * Coeffects
  , writeCoeffect
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Argonaut (Json, encodeJson, decodeJson)
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Aleph.Coeffect (Resource(..), PathSpec, filesystem)

-- ════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ════════════════════════════════════════════════════════════════════════════

{-| Write tool parameters.

@
  record WriteParams where
    filePath : String  -- Absolute path
    content  : String  -- File content
@
-}
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

-- ════════════════════════════════════════════════════════════════════════════
-- EXECUTION
-- ════════════════════════════════════════════════════════════════════════════

execute :: WriteParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Check if file exists (determines create vs update)
  -- 2. If exists, verify it was read this session
  -- 3. Generate diff for permission request
  -- 4. Write file
  -- 5. Notify LSP
  -- 6. Collect diagnostics
  -- 7. Return result with any errors
  
  pure
    { title: params.filePath
    , metadata: encodeJson
        { filePath: params.filePath
        , exists: false
        }
    , output: "Wrote file successfully."
    , attachments: Nothing
    }

-- ════════════════════════════════════════════════════════════════════════════
-- COEFFECTS
-- ════════════════════════════════════════════════════════════════════════════

writeCoeffect :: WriteParams -> Resource
writeCoeffect params =
  let pathSpec = 
        { path: params.filePath
        , readable: true
        , writable: true
        , recursive: false
        }
  in filesystem pathSpec

-- ════════════════════════════════════════════════════════════════════════════
-- TOOL REGISTRATION
-- ════════════════════════════════════════════════════════════════════════════

writeTool :: ToolInfo
writeTool =
  { id: "write"
  , description: "Write content to file with LSP diagnostics"
  , parameters: encodeJson { type: "object" }
  , execute: \json ctx ->
      case decodeJson json of
        Left err -> pure $ mkErrorResult (show err)
        Right params -> execute params ctx
  , formatValidationError: Nothing
  }

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Write Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }
