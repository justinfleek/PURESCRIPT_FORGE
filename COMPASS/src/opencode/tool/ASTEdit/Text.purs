{-|
Module      : Tool.ASTEdit.Text
Description : Text-based string replacement
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

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
  -- TODO: Proper unified diff computation
  "--- a/file\n+++ b/file\n"
