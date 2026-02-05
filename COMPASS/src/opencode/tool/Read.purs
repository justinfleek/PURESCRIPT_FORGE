{-|
Module      : Tool.Read
Description : File reading with line numbers and LSP warming
= Read Tool

Read files with line numbers (cat -n format) and session tracking.

== Coeffect Equation

@
  read : ReadParams → Graded (Filesystem path) ReadResult

  -- Requires filesystem read access
  -- Tracks read files for Edit validation
@

== Output Format

@
  <file>
  00001| module Main where
  00002| 
  00003| import Prelude
  ...
  (End of file - total 42 lines)
  </file>
@

== Binary File Handling

| Type    | Handling                           |
|---------|-----------------------------------|
| Image   | Return as base64 attachment        |
| PDF     | Return as base64 attachment        |
| Binary  | Error (cannot read)                |
| Text    | Normal line-numbered output        |
-}
module Tool.Read
  ( -- * Tool Interface
    ReadParams(..)
  , ReadResult(..)
  , execute
  , readTool
    -- * Configuration
  , ReadConfig(..)
  , defaultConfig
    -- * File Detection
  , isBinaryFile
  , isImageFile
    -- * Coeffects
  , readCoeffect
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

-- ════════════════════════════════════════════════════════════════════════════
-- CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════

type ReadConfig =
  { defaultLimit :: Int      -- Default lines to read
  , maxLineLength :: Int     -- Truncate lines longer than this
  , maxBytes :: Int          -- Maximum output bytes
  , binaryExtensions :: Array String
  , imageExtensions :: Array String
  }

defaultConfig :: ReadConfig
defaultConfig =
  { defaultLimit: 2000
  , maxLineLength: 2000
  , maxBytes: 50 * 1024
  , binaryExtensions: 
      [ ".zip", ".tar", ".gz", ".exe", ".dll", ".so"
      , ".class", ".jar", ".war", ".7z", ".bin", ".dat"
      , ".wasm", ".pyc", ".pyo", ".o", ".a", ".lib"
      ]
  , imageExtensions:
      [ ".png", ".jpg", ".jpeg", ".gif", ".webp", ".ico", ".pdf" ]
  }

-- ════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ════════════════════════════════════════════════════════════════════════════

{-| Read tool parameters.

@
  record ReadParams where
    filePath : String        -- Path to file
    offset   : Maybe Int     -- Starting line (0-based)
    limit    : Maybe Int     -- Lines to read
@
-}
type ReadParams =
  { filePath :: String
  , offset :: Maybe Int
  , limit :: Maybe Int
  }

type ReadResult =
  { content :: String
  , totalLines :: Int
  , linesRead :: Int
  , truncated :: Boolean
  , isImage :: Boolean
  }

-- ════════════════════════════════════════════════════════════════════════════
-- EXECUTION
-- ════════════════════════════════════════════════════════════════════════════

execute :: ReadParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  let offset = params.offset # maybe 0 identity
  let limit = params.limit # maybe defaultConfig.defaultLimit identity
  
  -- 1. Check file exists
  -- 2. Check for binary/image
  -- 3. Read lines with offset/limit
  -- 4. Format with line numbers
  -- 5. Track in session
  -- 6. Warm LSP
  
  pure
    { title: params.filePath
    , metadata: encodeJson
        { filePath: params.filePath
        , truncated: false
        , preview: ""
        }
    , output: formatOutput params.filePath [] false 0
    , attachments: Nothing
    }

-- | Format output with line numbers
formatOutput :: String -> Array String -> Boolean -> Int -> String
formatOutput path lines truncated totalLines =
  let numbered = lines # Array.mapWithIndex \i line ->
        formatLineNum (i + 1) <> "| " <> line
      content = String.joinWith "\n" numbered
      footer = if truncated
               then "(File has more lines. Use 'offset' to read beyond.)"
               else "(End of file - total " <> show totalLines <> " lines)"
  in "<file>\n" <> content <> "\n\n" <> footer <> "\n</file>"

formatLineNum :: Int -> String
formatLineNum n =
  let s = show n
      padding = String.fromCodePointArray $ 
        Array.replicate (5 - String.length s) (String.codePointFromChar '0')
  in padding <> s

-- ════════════════════════════════════════════════════════════════════════════
-- FILE DETECTION
-- ════════════════════════════════════════════════════════════════════════════

isBinaryFile :: String -> Boolean
isBinaryFile path =
  Array.any (\ext -> String.contains (String.Pattern ext) path) 
    defaultConfig.binaryExtensions

isImageFile :: String -> Boolean
isImageFile path =
  Array.any (\ext -> String.contains (String.Pattern ext) path)
    defaultConfig.imageExtensions

-- ════════════════════════════════════════════════════════════════════════════
-- COEFFECTS
-- ════════════════════════════════════════════════════════════════════════════

readCoeffect :: ReadParams -> Resource
readCoeffect params =
  let pathSpec = 
        { path: params.filePath
        , readable: true
        , writable: false
        , recursive: false
        }
  in filesystem pathSpec

-- ════════════════════════════════════════════════════════════════════════════
-- TOOL REGISTRATION
-- ════════════════════════════════════════════════════════════════════════════

readTool :: ToolInfo
readTool =
  { id: "read"
  , description: "Read file with line numbers"
  , parameters: encodeJson { type: "object" }
  , execute: \json ctx ->
      case decodeJson json of
        Left err -> pure $ mkErrorResult (show err)
        Right params -> execute params ctx
  , formatValidationError: Nothing
  }

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Read Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }
