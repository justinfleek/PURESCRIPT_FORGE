{-|
Module      : Tool.Multiedit
Description : Multiple sequential edits on a single file
= Multiedit Tool

This tool performs multiple sequential edit operations on a single file.
It's more efficient than calling the Edit tool multiple times and ensures
atomic application of related changes.

== Coeffect Equation

@
  multiedit : MultieditParams -> Graded (Filesystem path * IO) ToolResult

  -- Requires:
  -- 1. Filesystem write access to the target file
  -- 2. IO for reading current content
@

== Operation Sequence

Edits are applied in order:
@
  Original -> Edit 1 -> Edit 2 -> ... -> Edit N -> Final
@

Each edit operates on the result of the previous edit, allowing
dependent changes to be made in sequence.

== Use Cases

1. Renaming a variable throughout a file
2. Making multiple related fixes in one pass
3. Refactoring that requires coordinated changes
4. Updating imports and usages together

== Error Handling

If any edit fails, the entire operation is rolled back and the
file is left in its original state.
-}
module Tool.Multiedit
  ( -- * Tool Interface
    MultieditParams(..)
  , execute
  , multieditTool
    -- * Edit Types
  , Edit(..)
    -- * Helpers
  , applyEdits
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.Foldable (foldM)
import Data.String as String
import Data.Argonaut (Json, class EncodeJson, encodeJson, decodeJson, (.:), (.:?))
import Data.Maybe as Maybe
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo, ToolMetadata(..))
import Aleph.Coeffect (Resource(..))
import Tool.ASTEdit.FFI.FileIO (readFile, writeFile)
import Tool.ASTEdit.Text (applyText, TextParams)

-- ============================================================================
-- TYPES
-- ============================================================================

{-| Single edit operation.

@
  record Edit where
    filePath   : String           -- Target file (should match parent)
    oldString  : String           -- Text to replace
    newString  : String           -- Replacement text
    replaceAll : Maybe Boolean    -- Replace all occurrences
@
-}
type Edit =
  { filePath :: String
  , oldString :: String
  , newString :: String
  , replaceAll :: Maybe Boolean
  }

{-| Parameters for multiedit tool.

@
  record MultieditParams where
    filePath : String       -- The absolute path to the file
    edits    : Array Edit   -- Edits to apply sequentially
@
-}
type MultieditParams =
  { filePath :: String
  , edits :: Array Edit
  }

-- ============================================================================
-- TOOL INTERFACE
-- ============================================================================

{-| Execute multiedit tool.

Applies all edits sequentially to the target file.
-}
execute :: MultieditParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Read original file content
  readResult <- readFile params.filePath
  case readResult of
    Left err -> pure $ mkErrorResult ("Failed to read file: " <> err)
    Right originalContent -> do
      -- 2. Apply each edit in sequence
      case applyEdits originalContent params.edits of
        Left err -> pure $ mkErrorResult err
        Right finalContent -> do
          -- 3. Write final content
          writeResult <- writeFile params.filePath finalContent
          case writeResult of
            Left err -> pure $ mkErrorResult ("Failed to write file: " <> err)
            Right _ -> do
              -- 4. Return summary
              let numEdits = Array.length params.edits
              let relPath = relativePath params.filePath
              pure
                { title: relPath
                , metadata: MultieditMetadata
                    { filePath: params.filePath
                    , relativePath: relPath
                    , editsApplied: numEdits
                    }
                , output: "Successfully applied " <> show numEdits <> " edit(s) to " <> relPath <> "\n\n" <>
                         formatEditSummary params.edits
                , attachments: Nothing
                }

{-| Tool registration. -}
multieditTool :: ToolInfo
multieditTool =
  { id: "multiedit"
  , description: multieditDescription
  , parameters: encodeJson multieditSchema
  , execute: \json ctx ->
      case decodeMultieditParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> execute params ctx
  , formatValidationError: Just formatValidationError
  }

-- ============================================================================
-- HELPERS
-- ============================================================================

{-| Apply a sequence of edits to content.

Returns Left on first error, Right with final content on success.
-}
applyEdits :: String -> Array Edit -> Either String String
applyEdits content edits = foldM applyOne content edits
  where
    applyOne :: String -> Edit -> Either String String
    applyOne current edit = do
      let textParams :: TextParams
          textParams =
            { filePath: edit.filePath
            , oldString: edit.oldString
            , newString: edit.newString
            , replaceAll: Maybe.fromMaybe false edit.replaceAll
            }
      applyText textParams current

{-| Get relative path from absolute path. -}
relativePath :: String -> String
relativePath path =
  -- Extract relative path by removing common prefixes
  -- In production, would use actual worktree root
  case String.indexOf (String.Pattern "/") path of
    Just idx -> String.drop (idx + 1) path
    Nothing -> path

multieditDescription :: String
multieditDescription = 
  "Performs multiple sequential edit operations on a single file. " <>
  "Edits are applied in order, with each edit operating on the result " <>
  "of the previous edit."

multieditSchema :: Json
multieditSchema = encodeJson
  { type: "object"
  , properties:
      { filePath: { type: "string", description: "Absolute path to the file to edit" }
      , edits:
          { type: "array"
          , items:
              { type: "object"
              , properties:
                  { filePath: { type: "string", description: "Target file path (must match parent filePath)" }
                  , oldString: { type: "string", description: "Text to replace" }
                  , newString: { type: "string", description: "Replacement text" }
                  , replaceAll: { type: "boolean", description: "Replace all occurrences (default: false)" }
                  }
              , required: ["filePath", "oldString", "newString"]
              }
          , description: "Array of edits to apply sequentially"
          , minItems: 1
          }
      }
  , required: ["filePath", "edits"]
  }

decodeMultieditParams :: Json -> Either String MultieditParams
decodeMultieditParams json = do
  obj <- decodeJson json
  filePath <- obj .: "filePath" >>= decodeJson
  edits <- obj .: "edits" >>= decodeJson
  pure { filePath, edits }

-- | Format edit summary for output
formatEditSummary :: Array Edit -> String
formatEditSummary edits =
  if Array.null edits
  then ""
  else "Edits applied:\n" <>
       String.joinWith "\n" (Array.mapWithIndex formatEdit edits)
  where
    formatEdit idx edit =
      let replaceAllText = case edit.replaceAll of
            Just true -> " (all occurrences)"
            _ -> ""
      in "  " <> show (idx + 1) <> ". Replace \"" <>
         String.take 50 edit.oldString <> "\" with \"" <>
         String.take 50 edit.newString <> "\"" <> replaceAllText

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Multiedit Error"
  , metadata: ErrorMetadata { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatValidationError :: Json -> String
formatValidationError _ = "Invalid multiedit parameters"

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
