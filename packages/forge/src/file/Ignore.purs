{-|
Module      : Forge.File.Ignore
Description : File ignore patterns

Handles .gitignore-style ignore patterns for file operations.
Supports loading patterns from .gitignore files and matching
file paths against patterns.

== Coeffect Equation

@
  loadGitignore : String -> Graded Filesystem (Array String)
  shouldIgnore  : String -> Array String -> Boolean
@
-}
module Forge.File.Ignore
  ( -- * Pattern Matching
    shouldIgnore
  , matchPattern
    -- * Pattern Loading
  , loadGitignore
  , loadIgnoreFile
    -- * Default Patterns
  , defaultPatterns
  , codegenPatterns
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)

-- ============================================================================
-- FFI
-- ============================================================================

-- | Read file contents via FFI
foreign import readFileFFI :: String -> Aff (Either String String)

-- | Check if file exists via FFI
foreign import fileExistsFFI :: String -> Aff Boolean

-- ============================================================================
-- PATTERN MATCHING
-- ============================================================================

{-| Check if a file path should be ignored.

Matches path against an array of glob-like patterns.
-}
shouldIgnore :: String -> Array String -> Boolean
shouldIgnore path patterns =
  Array.any (\pattern -> matchPattern pattern path) patterns

{-| Match a single pattern against a path.

Supports basic glob patterns:
- `*` matches any sequence of characters except `/`
- `**` matches any sequence of characters including `/`
- Patterns ending with `/` match directories
- Patterns starting with `!` are negations (not supported yet)
-}
matchPattern :: String -> String -> Boolean
matchPattern pattern path
  -- Empty pattern matches nothing
  | String.null pattern = false
  -- Direct match
  | pattern == path = true
  -- Pattern ends with / - directory match
  | endsWith "/" pattern =
      let dir = String.dropRight 1 pattern
      in startsWith dir path ||
         String.contains (String.Pattern ("/" <> dir <> "/")) path
  -- Pattern contains ** - recursive match
  | String.contains (String.Pattern "**") pattern =
      matchGlobstar pattern path
  -- Pattern contains * - simple wildcard
  | String.contains (String.Pattern "*") pattern =
      matchWildcard pattern path
  -- Substring match (for simple patterns like "node_modules")
  | otherwise =
      String.contains (String.Pattern pattern) path ||
      String.contains (String.Pattern ("/" <> pattern)) path ||
      endsWith ("/" <> pattern) path
  where
    startsWith prefix str = String.take (String.length prefix) str == prefix
    endsWith suffix str = String.takeRight (String.length suffix) str == suffix

{-| Match pattern with * wildcard. -}
matchWildcard :: String -> String -> Boolean
matchWildcard pattern path =
  let parts = String.split (String.Pattern "*") pattern
  in case Array.uncons parts of
    Nothing -> false
    Just { head: first, tail: rest } ->
      startsWith first path &&
      matchWildcardRest rest (String.drop (String.length first) path)
  where
    startsWith prefix str = String.take (String.length prefix) str == prefix

matchWildcardRest :: Array String -> String -> Boolean
matchWildcardRest parts remaining =
  case Array.uncons parts of
    Nothing -> true
    Just { head: part, tail: rest } ->
      if String.null part
        then matchWildcardRest rest remaining
        else case String.indexOf (String.Pattern part) remaining of
          Nothing -> false
          Just idx -> matchWildcardRest rest (String.drop (idx + String.length part) remaining)

{-| Match pattern with ** globstar. -}
matchGlobstar :: String -> String -> Boolean
matchGlobstar pattern path =
  -- Split on ** and check if all parts match in order
  let parts = String.split (String.Pattern "**") pattern
  in case Array.uncons parts of
    Nothing -> false
    Just { head: first, tail: rest } ->
      (String.null first || startsWith first path) &&
      matchGlobstarRest rest path
  where
    startsWith prefix str = String.take (String.length prefix) str == prefix

matchGlobstarRest :: Array String -> String -> Boolean
matchGlobstarRest parts remaining =
  case Array.uncons parts of
    Nothing -> true
    Just { head: part, tail: rest } ->
      if String.null part
        then matchGlobstarRest rest remaining
        else String.contains (String.Pattern part) remaining

-- ============================================================================
-- PATTERN LOADING
-- ============================================================================

{-| Load patterns from a .gitignore file.

Returns empty array if file doesn't exist.
-}
loadGitignore :: String -> Aff (Either String (Array String))
loadGitignore directory = loadIgnoreFile (directory <> "/.gitignore")

{-| Load patterns from any ignore file.

Parses the file and returns an array of patterns.
Lines starting with # are comments.
Empty lines are skipped.
-}
loadIgnoreFile :: String -> Aff (Either String (Array String))
loadIgnoreFile filePath = do
  exists <- fileExistsFFI filePath
  if not exists
    then pure $ Right []
    else do
      readResult <- readFileFFI filePath
      case readResult of
        Left err -> pure $ Left err
        Right content -> pure $ Right $ parseIgnoreFile content

{-| Parse ignore file content into patterns. -}
parseIgnoreFile :: String -> Array String
parseIgnoreFile content =
  content
    # String.split (String.Pattern "\n")
    # map String.trim
    # Array.filter isValidPattern

{-| Check if a line is a valid pattern (not empty, not comment). -}
isValidPattern :: String -> Boolean
isValidPattern line =
  not (String.null line) &&
  not (String.take 1 line == "#")

-- ============================================================================
-- DEFAULT PATTERNS
-- ============================================================================

{-| Default ignore patterns for common directories. -}
defaultPatterns :: Array String
defaultPatterns = 
  [ "node_modules"
  , ".git"
  , "dist"
  , "build"
  , ".next"
  , "*.log"
  , ".DS_Store"
  , "Thumbs.db"
  , ".env"
  , ".env.local"
  , "*.swp"
  , "*.swo"
  , "*~"
  ]

{-| Patterns for generated/codegen directories. -}
codegenPatterns :: Array String
codegenPatterns =
  [ "output"           -- PureScript output
  , ".spago"           -- Spago cache
  , ".psci_modules"    -- PSCI modules
  , "target"           -- Rust/Maven target
  , "__pycache__"      -- Python cache
  , ".pytest_cache"    -- Pytest cache
  , "coverage"         -- Test coverage
  , ".nyc_output"      -- NYC coverage
  , ".turbo"           -- Turborepo cache
  , ".vercel"          -- Vercel build
  , ".netlify"         -- Netlify build
  ]
