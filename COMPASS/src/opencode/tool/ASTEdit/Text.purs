{-|
Module      : Tool.ASTEdit.Text
Description : Text-based string replacement
= Text Editing Mode

Exact string replacement for simple edits.

== Coeffect Equation

@
  text : TextParams → Graded (Filesystem path) EditResult
@

== Constraints

1. File MUST be read before editing
2. oldString must match exactly once (or use replaceAll)
3. oldString and newString must differ

== Usage

@
  { filePath: "src/Main.purs"
  , oldString: "foo"
  , newString: "bar"
  , replaceAll: false
  }
@
-}
module Tool.ASTEdit.Text
  ( -- * Parameters
    TextParams(..)
    -- * Execution
  , applyText
    -- * Validation
  , TextError(..)
  , validateText
    -- * Utilities
  , countOccurrences
  , computeDiff
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.String as String
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Effect.Aff (Aff)

import Tool.ASTEdit.Types (EditResult, FileChange, ChangeType(..))

-- ════════════════════════════════════════════════════════════════════════════
-- PARAMETERS
-- ════════════════════════════════════════════════════════════════════════════

type TextParams =
  { filePath :: String
  , oldString :: String
  , newString :: String
  , replaceAll :: Boolean
  }

-- ════════════════════════════════════════════════════════════════════════════
-- ERRORS
-- ════════════════════════════════════════════════════════════════════════════

data TextError
  = FileNotRead String
  | OldStringNotFound
  | MultipleMatches Int
  | IdenticalStrings
  | FileNotFound String
  | PermissionDenied String

derive instance eqTextError :: Eq TextError
derive instance genericTextError :: Generic TextError _

instance showTextError :: Show TextError where
  show = genericShow

-- ════════════════════════════════════════════════════════════════════════════
-- EXECUTION
-- ════════════════════════════════════════════════════════════════════════════

{-| Apply text-based edit.

1. Read current content
2. Count matches
3. Validate
4. Replace
5. Write back
-}
applyText :: TextParams -> String -> Either TextError String
applyText params content = do
  -- Validate
  _ <- validateText params content
  
  -- Apply replacement
  let newContent = if params.replaceAll
        then String.replaceAll 
               (String.Pattern params.oldString) 
               (String.Replacement params.newString) 
               content
        else replaceFirst params.oldString params.newString content
  
  Right newContent

-- ════════════════════════════════════════════════════════════════════════════
-- VALIDATION
-- ════════════════════════════════════════════════════════════════════════════

validateText :: TextParams -> String -> Either TextError Unit
validateText params content
  | params.oldString == params.newString = Left IdenticalStrings
  | String.null params.oldString = Left OldStringNotFound
  | otherwise =
      let count = countOccurrences params.oldString content
      in case count of
        0 -> Left OldStringNotFound
        1 -> Right unit
        n -> if params.replaceAll 
             then Right unit 
             else Left (MultipleMatches n)

-- ════════════════════════════════════════════════════════════════════════════
-- UTILITIES
-- ════════════════════════════════════════════════════════════════════════════

countOccurrences :: String -> String -> Int
countOccurrences needle haystack =
  go 0 haystack
  where
    go count str =
      case String.indexOf (String.Pattern needle) str of
        Nothing -> count
        Just idx ->
          let rest = String.drop (idx + String.length needle) str
          in go (count + 1) rest

replaceFirst :: String -> String -> String -> String
replaceFirst old new str =
  case String.indexOf (String.Pattern old) str of
    Nothing -> str
    Just idx ->
      let before = String.take idx str
          after = String.drop (idx + String.length old) str
      in before <> new <> after

computeDiff :: String -> String -> String
computeDiff old new =
  let oldLines = String.split (String.Pattern "\n") old
      newLines = String.split (String.Pattern "\n") new
      diffLines = computeDiffLines oldLines newLines
  in "--- a/file\n+++ b/file\n" <> String.joinWith "\n" diffLines

-- | Compute unified diff between two line arrays
computeDiffLines :: Array String -> Array String -> Array String
computeDiffLines oldLines newLines =
  let oldLen = Array.length oldLines
      newLen = Array.length newLines
      -- Simple line-by-line comparison
      -- In production, would use Myers diff algorithm or similar
      diff = computeDiffLinesImpl oldLines newLines 0 0 []
  in diff

-- | Compute diff lines with context
computeDiffLinesImpl :: Array String -> Array String -> Int -> Int -> Array String -> Array String
computeDiffLinesImpl oldLines newLines oldIdx newIdx acc
  | oldIdx >= Array.length oldLines && newIdx >= Array.length newLines = Array.reverse acc
  | oldIdx >= Array.length oldLines = 
      -- All remaining new lines are additions
      case Array.index newLines newIdx of
        Just newLine -> computeDiffLinesImpl oldLines newLines oldIdx (newIdx + 1) 
          (Array.cons ("+" <> newLine) acc)
        Nothing -> Array.reverse acc
  | newIdx >= Array.length newLines = 
      -- All remaining old lines are deletions
      case Array.index oldLines oldIdx of
        Just oldLine -> computeDiffLinesImpl oldLines newLines (oldIdx + 1) newIdx 
          (Array.cons ("-" <> oldLine) acc)
        Nothing -> Array.reverse acc
  | otherwise =
      case Array.index oldLines oldIdx, Array.index newLines newIdx of
        Just oldLine, Just newLine ->
          if oldLine == newLine
          then
            -- Lines match, include as context
            computeDiffLinesImpl oldLines newLines (oldIdx + 1) (newIdx + 1)
              (Array.cons (" " <> oldLine) acc)
          else
            -- Lines differ, show deletion and addition
            computeDiffLinesImpl oldLines newLines (oldIdx + 1) (newIdx + 1)
              (Array.cons ("+" <> newLine) (Array.cons ("-" <> oldLine) acc))
        _, _ -> Array.reverse acc
