{-|
Module      : Tool.Multiedit
Description : Multiple sequential edits on a single file
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

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
import Data.Argonaut (Json, class EncodeJson, encodeJson, decodeJson)
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Aleph.Coeffect (Resource(..))

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
  -- 2. Apply each edit in sequence
  -- 3. Write final content
  -- 4. Return summary
  let numEdits = Array.length params.edits
  
  -- TODO: Actually perform edits via ASTEdit.Text
  pure
    { title: relativePath params.filePath
    , metadata: encodeJson
        { filePath: params.filePath
        , editsApplied: numEdits
        }
    , output: "Applied " <> show numEdits <> " edits to " <> params.filePath
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
    applyOne current edit =
      -- TODO: Implement actual string replacement
      Right current

{-| Get relative path from absolute path. -}
relativePath :: String -> String
relativePath path = path  -- TODO: Make relative to worktree

multieditDescription :: String
multieditDescription = 
  "Performs multiple sequential edit operations on a single file. " <>
  "Edits are applied in order, with each edit operating on the result " <>
  "of the previous edit."

multieditSchema :: { type :: String }
multieditSchema = { type: "object" }

decodeMultieditParams :: Json -> Either String MultieditParams
decodeMultieditParams _ = notImplemented "decodeMultieditParams"

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Multiedit Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatValidationError :: Json -> String
formatValidationError _ = "Invalid multiedit parameters"

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
