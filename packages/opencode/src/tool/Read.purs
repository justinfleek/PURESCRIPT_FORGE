-- | Read.purs - File reading tool
-- | Mirrors opencode/src/tool/read.ts
-- |
-- | Reads files from the local filesystem. This tool:
-- | - Reads files with line numbers (cat -n format)
-- | - Supports offset/limit for large files
-- | - Tracks read files in session for Edit validation
-- | - Can read binary files (images) with base64 encoding
-- |
-- | IMPORTANT: This is the ONLY way to read files - no grep/cat/head/tail
-- | See Lean4 proofs in proofs/lean/Opencode/Proofs/FileReading.lean
module Tool.Read where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Argonaut (Json, encodeJson, decodeJson)

-- Import canonical types
import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Opencode.Types.File (FileReadResult, CompleteFileRead, BannedFileOperation)

-- | Read tool parameters
-- | Matches the TypeScript Zod schema in read.ts
type ReadParams =
  { filePath :: String           -- Absolute path to the file
  , offset :: Maybe Int          -- Line number to start from (0-based)
  , limit :: Maybe Int           -- Number of lines to read (default 2000)
  }

-- | Read result metadata
type ReadMetadata =
  { filePath :: String
  , totalLines :: Int            -- Total lines in file
  , linesRead :: Int             -- Lines actually returned
  , offset :: Int                -- Starting line
  , truncated :: Boolean         -- Whether output was truncated
  , encoding :: String           -- "utf8" or "base64" for binary
  }

-- | Default configuration
type ReadConfig =
  { defaultLimit :: Int          -- Default line limit
  , maxLineLength :: Int         -- Max characters per line before truncation
  , binaryExtensions :: Array String  -- Extensions to read as base64
  }

defaultConfig :: ReadConfig
defaultConfig =
  { defaultLimit: 2000
  , maxLineLength: 2000
  , binaryExtensions: [".png", ".jpg", ".jpeg", ".gif", ".webp", ".ico", ".pdf"]
  }

-- | Check if file is binary based on extension
isBinaryFile :: String -> Boolean
isBinaryFile path = 
  Array.any (\ext -> String.contains (String.Pattern ext) path) defaultConfig.binaryExtensions

-- | Format line with line number (cat -n style)
-- | Output: "    1\tcontent"
formatLine :: Int -> String -> String
formatLine lineNum content =
  let numStr = show lineNum
      padding = String.fromCodePointArray (Array.replicate (5 - String.length numStr) (String.codePointFromChar ' '))
  in padding <> numStr <> "\t" <> content

-- | Execute file read
-- | Main entry point called by tool registry
execute :: ReadParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- TODO:
  -- 1. Check file exists
  -- 2. Check file permissions
  -- 3. Read file contents
  -- 4. Apply offset/limit
  -- 5. Format with line numbers
  -- 6. Track in session state (for Edit validation)
  -- 7. Return result
  let 
    offset = fromMaybe 0 params.offset
    limit = fromMaybe defaultConfig.defaultLimit params.limit
  
  pure
    { title: params.filePath
    , metadata: encodeJson (mkMetadata params)
    , output: "TODO: Implement file reading via FFI\nWould read " <> params.filePath <> " from line " <> show offset
    , attachments: Nothing
    }

-- | Create metadata
mkMetadata :: ReadParams -> ReadMetadata
mkMetadata params =
  { filePath: params.filePath
  , totalLines: 0
  , linesRead: 0
  , offset: fromMaybe 0 params.offset
  , truncated: false
  , encoding: if isBinaryFile params.filePath then "base64" else "utf8"
  }

-- | Create error result
mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Read Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

-- | Tool registration info
readTool :: ToolInfo
readTool =
  { id: "read"
  , description: "Reads a file from the local filesystem"
  , parameters: encodeJson readParamsSchema
  , execute: \json ctx ->
      case decodeJson json of
        Left err -> pure $ mkErrorResult (show err)
        Right params -> execute params ctx
  , formatValidationError: Nothing
  }

-- | JSON schema placeholder
readParamsSchema :: { type :: String }
readParamsSchema = notImplemented "readParamsSchema"

-- | Helper to unwrap Maybe with default
fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe def = case _ of
  Nothing -> def
  Just a -> a

-- Helpers
notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
