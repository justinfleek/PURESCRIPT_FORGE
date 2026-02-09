{-|
Module      : Forge.File.Ripgrep
Description : Ripgrep integration

Provides a PureScript interface to ripgrep (rg) for fast file content searching.
Uses the ripgrep binary via child process execution.

== Coeffect Equation

@
  search      : RipgrepOptions -> Graded (Filesystem * Container) (Array RipgrepMatch)
  isAvailable : Unit -> Graded Container Boolean
@

== Output Format

Ripgrep JSON output is parsed into typed matches with file, line, column, and text.
-}
module Forge.File.Ripgrep
  ( -- * Types
    RipgrepOptions
  , RipgrepMatch
  , RipgrepResult
    -- * Operations
  , search
  , searchJson
  , isAvailable
    -- * Utilities
  , buildArgs
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.String as String
import Data.Argonaut (Json, decodeJson, (.:), (.:?))
import Data.Argonaut.Parser (jsonParser)
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Ripgrep search options
type RipgrepOptions =
  { pattern :: String               -- Regex pattern to search for
  , path :: String                  -- Directory or file to search
  , include :: Maybe String         -- File glob pattern (e.g., "*.ts")
  , exclude :: Maybe (Array String) -- Patterns to exclude
  , maxResults :: Maybe Int         -- Maximum number of results
  , caseSensitive :: Maybe Boolean  -- Case-sensitive search (default: smart case)
  , wholeWord :: Maybe Boolean      -- Match whole words only
  , contextLines :: Maybe Int       -- Lines of context before/after
  }

-- | A single ripgrep match
type RipgrepMatch =
  { file :: String      -- File path
  , line :: Int         -- Line number (1-indexed)
  , column :: Int       -- Column number (1-indexed)
  , text :: String      -- Matched line text
  , matchStart :: Int   -- Start position of match within line
  , matchEnd :: Int     -- End position of match within line
  }

-- | Ripgrep search result
type RipgrepResult =
  { matches :: Array RipgrepMatch
  , fileCount :: Int
  , truncated :: Boolean
  }

-- ============================================================================
-- FFI
-- ============================================================================

-- | Execute ripgrep via FFI
foreign import executeRipgrepFFI :: Array String -> String -> Aff (Either String { stdout :: String, exitCode :: Int })

-- | Check if ripgrep is available
foreign import checkRipgrepFFI :: Aff Boolean

-- ============================================================================
-- OPERATIONS
-- ============================================================================

{-| Check if ripgrep is available on the system. -}
isAvailable :: Aff Boolean
isAvailable = checkRipgrepFFI

{-| Search files using ripgrep.

Returns an array of matches. Uses text output parsing.
-}
search :: RipgrepOptions -> Aff (Either String RipgrepResult)
search options = do
  let args = buildArgs options
  result <- executeRipgrepFFI args options.path
  case result of
    Left err -> pure $ Left err
    Right { stdout, exitCode } ->
      -- Exit code 0 = matches found
      -- Exit code 1 = no matches found (not an error)
      -- Exit code 2+ = actual error
      if exitCode >= 2
        then pure $ Left ("ripgrep error (exit " <> show exitCode <> ")")
        else pure $ Right $ parseTextOutput stdout options.maxResults

{-| Search files using ripgrep with JSON output.

Returns parsed JSON matches. Slower but more detailed.
-}
searchJson :: RipgrepOptions -> Aff (Either String RipgrepResult)
searchJson options = do
  let args = buildArgs options <> ["--json"]
  result <- executeRipgrepFFI args options.path
  case result of
    Left err -> pure $ Left err
    Right { stdout, exitCode } ->
      if exitCode >= 2
        then pure $ Left ("ripgrep error (exit " <> show exitCode <> ")")
        else case parseJsonOutput stdout of
          Left parseErr -> pure $ Left parseErr
          Right matches -> pure $ Right
            { matches
            , fileCount: Array.length $ Array.nub $ map _.file matches
            , truncated: maybe false (\max -> Array.length matches >= max) options.maxResults
            }

-- ============================================================================
-- ARGUMENT BUILDING
-- ============================================================================

{-| Build ripgrep command line arguments. -}
buildArgs :: RipgrepOptions -> Array String
buildArgs options =
  -- Basic args
  [ "-n"           -- Line numbers
  , "-H"           -- Filenames
  , "--column"     -- Column numbers
  , "--no-heading" -- No grouped output
  ]
  -- Include pattern
  <> maybe [] (\g -> ["--glob", g]) options.include
  -- Exclude patterns
  <> Array.foldMap (\e -> ["--glob", "!" <> e]) (fromMaybe [] options.exclude)
  -- Max results
  <> maybe [] (\m -> ["--max-count", show m]) options.maxResults
  -- Case sensitivity
  <> case options.caseSensitive of
       Just true -> ["-s"]  -- Case sensitive
       Just false -> ["-i"] -- Case insensitive
       Nothing -> ["-S"]    -- Smart case (default)
  -- Whole word
  <> if fromMaybe false options.wholeWord then ["-w"] else []
  -- Context lines
  <> maybe [] (\c -> ["-C", show c]) options.contextLines
  -- Pattern (must be after flags)
  <> ["-e", options.pattern]

-- ============================================================================
-- OUTPUT PARSING
-- ============================================================================

{-| Parse ripgrep text output.

Format: file:line:column:text
-}
parseTextOutput :: String -> Maybe Int -> RipgrepResult
parseTextOutput output maxResults =
  let lines = String.split (String.Pattern "\n") output
      matches = Array.mapMaybe parseTextLine lines
      limited = maybe matches (\max -> Array.take max matches) maxResults
  in { matches: limited
     , fileCount: Array.length $ Array.nub $ map _.file limited
     , truncated: maybe false (\max -> Array.length matches >= max) maxResults
     }

{-| Parse a single line of ripgrep text output. -}
parseTextLine :: String -> Maybe RipgrepMatch
parseTextLine line = do
  -- Format: file:line:column:text
  let parts = String.split (String.Pattern ":") line
  file <- Array.index parts 0
  lineNumStr <- Array.index parts 1
  colStr <- Array.index parts 2
  lineNum <- parseIntMaybe lineNumStr
  col <- parseIntMaybe colStr
  let text = String.joinWith ":" $ Array.drop 3 parts
  pure
    { file
    , line: lineNum
    , column: col
    , text
    , matchStart: col - 1
    , matchEnd: col -- Approximate, would need match length
    }

{-| Parse ripgrep JSON output. -}
parseJsonOutput :: String -> Either String (Array RipgrepMatch)
parseJsonOutput output =
  let lines = String.split (String.Pattern "\n") output
      matches = Array.mapMaybe parseJsonLine lines
  in Right matches

{-| Parse a single line of ripgrep JSON output. -}
parseJsonLine :: String -> Maybe RipgrepMatch
parseJsonLine line
  | String.null line = Nothing
  | otherwise = case jsonParser line of
      Left _ -> Nothing
      Right json -> parseJsonMatch json

{-| Parse a ripgrep JSON match object. -}
parseJsonMatch :: Json -> Maybe RipgrepMatch
parseJsonMatch json = do
  obj <- hush $ decodeJson json
  msgType <- hush $ obj .: "type"
  if msgType /= "match"
    then Nothing
    else do
      dataObj <- hush $ obj .: "data"
      pathObj <- hush $ dataObj .: "path"
      file <- hush $ pathObj .: "text"
      lineNum <- hush $ dataObj .: "line_number"
      submatches <- hush $ dataObj .: "submatches"
      firstMatch <- Array.head submatches
      matchObj <- pure firstMatch
      matchStart <- hush $ matchObj .: "start"
      matchEnd <- hush $ matchObj .: "end"
      linesObj <- hush $ dataObj .: "lines"
      text <- hush $ linesObj .: "text"
      pure
        { file
        , line: lineNum
        , column: matchStart + 1
        , text: String.trim text
        , matchStart
        , matchEnd
        }

-- ============================================================================
-- HELPERS
-- ============================================================================

parseIntMaybe :: String -> Maybe Int
parseIntMaybe s = 
  let trimmed = String.trim s
  in if String.null trimmed
     then Nothing
     else case parseIntFFI trimmed of
       n | n >= 0 -> Just n
       _ -> Nothing

foreign import parseIntFFI :: String -> Int

hush :: forall a b. Either a b -> Maybe b
hush (Left _) = Nothing
hush (Right b) = Just b
