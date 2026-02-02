-- | Edit.purs - File editing tool (exact string replacement)
-- | Mirrors opencode/src/tool/edit.ts
-- |
-- | Performs exact string replacements in files. The tool enforces:
-- | - User must Read the file before editing (tracked in session)
-- | - oldString must be found exactly once (or use replaceAll)
-- | - Preserves exact indentation from file
module Tool.Edit where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.String as String
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Argonaut (Json, encodeJson, decodeJson)

-- Import canonical types
import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Opencode.Types.File (FileReadResult)

-- | Edit tool parameters
-- | Matches the TypeScript Zod schema in edit.ts
type EditParams =
  { filePath :: String           -- Absolute path to file
  , oldString :: String          -- Exact text to replace
  , newString :: String          -- Replacement text (must differ from oldString)
  , replaceAll :: Maybe Boolean  -- Replace all occurrences (default false)
  }

-- | Edit result metadata
type EditMetadata =
  { filePath :: String
  , matchCount :: Int            -- How many matches were found
  , replaced :: Int              -- How many replacements made
  , linesChanged :: Int          -- Number of lines affected
  }

-- | Validation errors specific to Edit tool
data EditError
  = FileNotRead String           -- Must read before editing
  | OldStringNotFound String     -- oldString not in file
  | MultipleMatches Int          -- Found multiple matches without replaceAll
  | IdenticalStrings             -- oldString equals newString
  | FileNotFound String          -- File doesn't exist
  | PermissionDenied String      -- Not allowed to edit this file

-- | Validate edit parameters
validateParams :: EditParams -> Either EditError Unit
validateParams params
  | params.oldString == params.newString = Left IdenticalStrings
  | String.null params.oldString = Left (OldStringNotFound "oldString cannot be empty")
  | otherwise = Right unit

-- | Count occurrences of a substring
countOccurrences :: String -> String -> Int
countOccurrences needle haystack = 
  -- TODO: Implement proper counting
  notImplemented "countOccurrences"

-- | Execute file edit
-- | Main entry point called by tool registry
execute :: EditParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Validate parameters
  case validateParams params of
    Left err -> pure $ mkErrorResult (showEditError err)
    Right _ -> executeImpl params ctx

-- | Internal implementation after validation
executeImpl :: EditParams -> ToolContext -> Aff ToolResult
executeImpl params ctx = do
  -- TODO: 
  -- 1. Check session for prior Read of this file
  -- 2. Read current file contents
  -- 3. Count matches
  -- 4. If count == 0, error
  -- 5. If count > 1 && not replaceAll, error
  -- 6. Perform replacement(s)
  -- 7. Write file back
  -- 8. Return result with diff
  pure
    { title: "Edit " <> params.filePath
    , metadata: encodeJson mkEmptyMetadata
    , output: "TODO: Implement file editing via FFI"
    , attachments: Nothing
    }
  where
    mkEmptyMetadata :: EditMetadata
    mkEmptyMetadata = 
      { filePath: params.filePath
      , matchCount: 0
      , replaced: 0
      , linesChanged: 0
      }

-- | Create error result
mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Edit Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

-- | Show edit error as string
showEditError :: EditError -> String
showEditError = case _ of
  FileNotRead path -> "Must read file before editing: " <> path
  OldStringNotFound msg -> "oldString not found in content: " <> msg
  MultipleMatches n -> "oldString found " <> show n <> " times - use replaceAll or provide more context"
  IdenticalStrings -> "oldString and newString must be different"
  FileNotFound path -> "File not found: " <> path
  PermissionDenied path -> "Permission denied: " <> path

-- | Tool registration info
editTool :: ToolInfo
editTool =
  { id: "edit"
  , description: "Performs exact string replacements in files"
  , parameters: encodeJson editParamsSchema
  , execute: \json ctx ->
      case decodeJson json of
        Left err -> pure $ mkErrorResult (show err)
        Right params -> execute params ctx
  , formatValidationError: Just formatError
  }

-- | Format validation error for better UX
formatError :: Json -> String
formatError _ = notImplemented "formatError"

-- | JSON schema placeholder
editParamsSchema :: { type :: String }
editParamsSchema = notImplemented "editParamsSchema"

-- Helpers
notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
