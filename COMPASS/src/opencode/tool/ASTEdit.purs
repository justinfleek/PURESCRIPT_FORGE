{-|
Module      : Tool.ASTEdit
Description : Unified editing system
= ASTEdit - Unified Editing Tool

Single interface for all code editing operations.

== Module Structure

@
  Tool.ASTEdit
  ├── Types       -- Core types (EditMode, Span, Change)
  ├── Structural  -- AST-based transformations
  ├── Text        -- String replacement
  └── Patch       -- Multi-file patches
@

== Coeffect Equation

@
  edit : EditParams → Graded (Filesystem paths ⊗ AST lang?) EditResult

  -- Mode determines coeffect:
  -- Structural: Filesystem ⊗ AST lang
  -- Text:       Filesystem
  -- Patch:      Filesystem (multiple paths)
@

== Mode Selection

The tool auto-selects mode based on input:

1. If `patchText` provided → Patch mode
2. If `operation` provided → Structural mode  
3. If `oldString`/`newString` provided → Text mode

== Usage Examples

=== Text Mode

@
  edit
    { filePath: "src/Main.purs"
    , oldString: "foo"
    , newString: "bar"
    }
@

=== Structural Mode

@
  edit
    { filePath: "src/Main.purs"
    , operation: Rename (Symbol "foo") (Symbol "bar")
    }
@

=== Patch Mode

@
  edit
    { patchText: \"\"\"
        *** Begin Patch
        *** Add File: src/New.purs
        +module New where
        *** End Patch
      \"\"\"
    }
@
-}
module Tool.ASTEdit
  ( -- * Tool Interface
    EditParams(..)
  , execute
  , editTool
    -- * Re-exports
  , module Tool.ASTEdit.Types
  , module ReExports
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Argonaut (Json, encodeJson, decodeJson)
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Aleph.Coeffect (Resource(..), PathSpec, ASTLanguage(..), filesystem, astRes, (⊗))

import Tool.ASTEdit.Types
import Tool.ASTEdit.Structural (EditOp, applyStructural) as ReExports
import Tool.ASTEdit.Text (TextParams, applyText, TextError) as Text
import Tool.ASTEdit.Patch (PatchParams, parsePatch, applyPatch, PatchError) as Patch
import Tool.ASTEdit.FFI.FileIO (readFile, writeFile)

-- ════════════════════════════════════════════════════════════════════════════
-- UNIFIED PARAMETERS
-- ════════════════════════════════════════════════════════════════════════════

{-| Unified edit parameters.

Provide ONE of:
- `oldString`/`newString` for text mode
- `operation` for structural mode
- `patchText` for patch mode
-}
type EditParams =
  { -- Common
    filePath :: Maybe String
  , dryRun :: Boolean
  , validate :: Boolean
    -- Text mode
  , oldString :: Maybe String
  , newString :: Maybe String
  , replaceAll :: Maybe Boolean
    -- Structural mode
  , operation :: Maybe ReExports.EditOp
    -- Patch mode
  , patchText :: Maybe String
  }

-- ════════════════════════════════════════════════════════════════════════════
-- MODE DETECTION
-- ════════════════════════════════════════════════════════════════════════════

detectMode :: EditParams -> EditMode
detectMode params
  | isJust params.patchText = Patch
  | isJust params.operation = Structural (detectLanguage params.filePath)
  | isJust params.oldString = Text
  | otherwise = Text
  where
    isJust (Just _) = true
    isJust Nothing = false

detectLanguage :: Maybe String -> ASTLanguage
detectLanguage = case _ of
  Nothing -> ASTUnknown ""
  Just path
    | hasExt ".purs" path -> ASTPureScript
    | hasExt ".hs" path -> ASTHaskell
    | hasExt ".lean" path -> ASTLean4
    | hasExt ".ts" path -> ASTTypeScript
    | hasExt ".tsx" path -> ASTTypeScript
    | hasExt ".nix" path -> ASTNix
    | hasExt ".py" path -> ASTPython
    | hasExt ".rs" path -> ASTRust
    | otherwise -> ASTUnknown ""
  where
    hasExt ext p = String.contains (String.Pattern ext) p

-- ════════════════════════════════════════════════════════════════════════════
-- EXECUTION
-- ════════════════════════════════════════════════════════════════════════════

execute :: EditParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  let mode = detectMode params
  
  case mode of
    Patch -> executePatch params ctx
    Structural lang -> executeStructural params lang ctx
    Text -> executeText params ctx

executePatch :: EditParams -> ToolContext -> Aff ToolResult
executePatch params ctx = do
  case params.patchText of
    Nothing -> pure $ mkErrorResult "patchText required for patch mode"
    Just patchText -> do
      result <- Patch.applyPatch { patchText }
      case result of
        Left err -> pure $ mkErrorResult (show err)
        Right changes -> pure
          { title: "Patch applied"
          , metadata: encodeJson
              { mode: "patch"
              , filesChanged: Array.length changes
              }
          , output: formatPatchOutput changes
          , attachments: Nothing
          }

executeStructural :: EditParams -> ASTLanguage -> ToolContext -> Aff ToolResult
executeStructural params lang ctx = do
  case params.filePath, params.operation of
    Just path, Just op -> do
      -- Read file content
      readResult <- readFile path
      case readResult of
        Left err -> pure $ mkErrorResult ("Failed to read file: " <> err)
        Right content -> do
          -- Apply structural edit
          editResult <- ReExports.applyStructural lang content op
          case editResult of
            Left err -> pure $ mkErrorResult ("Structural edit failed: " <> err)
            Right editResult' -> do
              if params.dryRun then
                -- Dry run: don't write, just return result
                pure
                  { title: "Structural edit (dry run): " <> path
                  , metadata: encodeJson
                      { mode: "structural"
                      , language: show lang
                      , dryRun: true
                      , filesChanged: editResult'.filesChanged
                      }
                  , output: "Dry run - would apply " <> show (Array.length editResult'.changes) <> " changes"
                  , attachments: Nothing
                  }
              else do
                -- Write result back to file
                case Array.head editResult'.changes of
                  Nothing -> pure $ mkErrorResult "No changes to apply"
                  Just change -> do
                    writeResult <- writeFile path change.newContent
                    case writeResult of
                      Left err -> pure $ mkErrorResult ("Failed to write file: " <> err)
                      Right _ -> pure
                        { title: "Structural edit applied: " <> path
                        , metadata: encodeJson
                            { mode: "structural"
                            , language: show lang
                            , filesChanged: editResult'.filesChanged
                            , success: editResult'.success
                            }
                        , output: "Applied structural edit successfully. " <> 
                                 show (Array.length editResult'.changes) <> " file(s) changed."
                        , attachments: Nothing
                        }
    _, _ -> pure $ mkErrorResult "filePath and operation required for structural mode"

executeText :: EditParams -> ToolContext -> Aff ToolResult
executeText params ctx = do
  case params.filePath, params.oldString, params.newString of
    Just path, Just old, Just new -> do
      -- Read file content
      readResult <- readFile path
      case readResult of
        Left err -> pure $ mkErrorResult ("Failed to read file: " <> err)
        Right content -> do
          let textParams = 
                { filePath: path
                , oldString: old
                , newString: new
                , replaceAll: params.replaceAll == Just true
                }
          case Text.applyText textParams content of
            Left err -> pure $ mkErrorResult (show err)
            Right newContent -> pure
          { title: "Edit " <> path
          , metadata: encodeJson
              { mode: "text"
              , filePath: path
              }
          , output: "Replaced successfully"
          , attachments: Nothing
          }
    _, _, _ -> pure $ mkErrorResult "filePath, oldString, newString required for text mode"

-- ════════════════════════════════════════════════════════════════════════════
-- OUTPUT FORMATTING
-- ════════════════════════════════════════════════════════════════════════════

formatPatchOutput :: Array FileChange -> String
formatPatchOutput changes =
  let summary = changes # map \c ->
        let prefix = case c.changeType of
              Add -> "A"
              Update -> "M"
              Delete -> "D"
              Move _ -> "R"
        in prefix <> " " <> c.filePath
  in "Updated files:\n" <> String.joinWith "\n" summary

-- ════════════════════════════════════════════════════════════════════════════
-- COEFFECTS
-- ════════════════════════════════════════════════════════════════════════════

editCoeffect :: EditParams -> Resource
editCoeffect params =
  let mode = detectMode params
  in case mode of
    Patch -> 
      filesystem { path: ".", readable: true, writable: true, recursive: true }
    
    Structural lang ->
      let pathSpec = { path: fromMaybe "." params.filePath
                     , readable: true, writable: true, recursive: false }
      in filesystem pathSpec ⊗ astRes lang
    
    Text ->
      let pathSpec = { path: fromMaybe "." params.filePath
                     , readable: true, writable: true, recursive: false }
      in filesystem pathSpec
  where
    fromMaybe def = case _ of
      Nothing -> def
      Just x -> x

-- ════════════════════════════════════════════════════════════════════════════
-- TOOL REGISTRATION
-- ════════════════════════════════════════════════════════════════════════════

editTool :: ToolInfo
editTool =
  { id: "edit"
  , description: "Unified code editing (text, structural, or patch mode)"
  , parameters: encodeJson { type: "object" }
  , execute: \json ctx ->
      case decodeJson json of
        Left err -> pure $ mkErrorResult (show err)
        Right params -> execute params ctx
  , formatValidationError: Nothing
  }

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Edit Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }
