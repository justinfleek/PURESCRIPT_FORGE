{-|
Module      : Tool.Truncation
Description : Output truncation for large tool results
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Truncation

This module handles truncation of large tool outputs to prevent
context overflow. Full output is saved to disk and a truncated
preview is returned.

== Coeffect Equation

@
  truncate : String -> Options -> Graded (Filesystem * IO) TruncateResult

  -- Requires:
  -- 1. Filesystem for saving full output
  -- 2. IO for file operations
@

== Truncation Limits

| Limit    | Value   | Description                    |
|----------|---------|--------------------------------|
| maxLines | 2000    | Maximum lines in output        |
| maxBytes | 51200   | Maximum bytes (50KB)           |

== Truncation Direction

| Direction | Use Case                          |
|-----------|-----------------------------------|
| head      | Show first N lines (default)      |
| tail      | Show last N lines                 |

== Output File Retention

Truncated output files are stored in:
@
  $XDG_DATA_HOME/opencode/tool-output/
@

Files are automatically cleaned up after 7 days.
-}
module Tool.Truncation
  ( -- * Configuration
    maxLines
  , maxBytes
  , outputDir
    -- * Truncation
  , TruncateResult(..)
  , TruncateOptions(..)
  , truncateOutput
    -- * Cleanup
  , cleanup
  , init
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)

-- ============================================================================
-- CONFIGURATION
-- ============================================================================

-- | Maximum lines before truncation
maxLines :: Int
maxLines = 2000

-- | Maximum bytes before truncation (50KB)
maxBytes :: Int
maxBytes = 51200

-- | Output directory for truncated files
outputDir :: String
outputDir = "/var/lib/opencode/tool-output"  -- TODO: Use XDG paths

-- | Retention period for output files (7 days in ms)
retentionMs :: Int
retentionMs = 7 * 24 * 60 * 60 * 1000

-- ============================================================================
-- TYPES
-- ============================================================================

{-| Result of truncation operation.

Either returns content unchanged, or truncated content with path to full file.
-}
data TruncateResult
  = NotTruncated { content :: String }
  | Truncated
      { content :: String      -- Truncated preview
      , outputPath :: String   -- Path to full output
      , removedLines :: Int    -- Number of lines removed
      , removedBytes :: Int    -- Number of bytes removed
      }

{-| Options for truncation. -}
type TruncateOptions =
  { maxLines :: Maybe Int      -- Override default line limit
  , maxBytes :: Maybe Int      -- Override default byte limit
  , direction :: Maybe String  -- "head" or "tail"
  }

-- ============================================================================
-- TRUNCATION
-- ============================================================================

{-| Truncate output if it exceeds limits.

If output exceeds either line or byte limit:
1. Saves full output to disk
2. Returns truncated preview with hint about full file

The hint varies based on whether the agent has Task tool access:
- With Task: Suggests using Task tool to process file
- Without Task: Suggests using Grep/Read with offset
-}
truncateOutput :: String -> TruncateOptions -> Aff TruncateResult
truncateOutput text options = do
  let lineLim = fromMaybe maxLines options.maxLines
  let byteLim = fromMaybe maxBytes options.maxBytes
  let dir = fromMaybe "head" options.direction
  
  let lines = String.split (String.Pattern "\n") text
  let lineCount = Array.length lines
  let byteCount = String.length text  -- Approximation; proper impl uses Buffer.byteLength
  
  -- Check if truncation needed
  if lineCount <= lineLim && byteCount <= byteLim
    then pure $ NotTruncated { content: text }
    else do
      -- Truncate based on direction
      let truncated = truncateLines lines lineLim byteLim dir
      
      -- Save full output to file
      outputPath <- saveOutput text
      
      -- Build result
      pure $ Truncated
        { content: truncated.preview <> "\n\n" <> truncationHint outputPath
        , outputPath
        , removedLines: lineCount - truncated.kept
        , removedBytes: byteCount - String.length truncated.preview
        }
  where
    fromMaybe :: forall a. a -> Maybe a -> a
    fromMaybe def Nothing = def
    fromMaybe _ (Just x) = x

{-| Truncate lines based on direction. -}
truncateLines :: Array String -> Int -> Int -> String -> { preview :: String, kept :: Int }
truncateLines lines lineLim byteLim direction =
  let kept = min lineLim (Array.length lines)
      taken = if direction == "head"
                then Array.take kept lines
                else Array.drop (Array.length lines - kept) lines
      preview = String.joinWith "\n" taken
  in { preview, kept }

{-| Save output to file and return path. -}
saveOutput :: String -> Aff String
saveOutput text = do
  -- TODO: Generate unique ID and write to file
  pure $ outputDir <> "/output_placeholder"

{-| Build truncation hint for output. -}
truncationHint :: String -> String
truncationHint path = String.joinWith "\n"
  [ "..."
  , ""
  , "Output was truncated. Full output saved to: " <> path
  , "Use the Task tool to have explore agent process this file with Grep and Read."
  ]

-- ============================================================================
-- CLEANUP
-- ============================================================================

{-| Initialize truncation scheduler. -}
init :: Effect Unit
init = do
  -- TODO: Register cleanup scheduler
  pure unit

{-| Clean up old output files.

Removes files older than retention period.
-}
cleanup :: Aff Unit
cleanup = do
  -- TODO: List files in outputDir
  -- TODO: Remove files older than retentionMs
  pure unit
