{-|
Module      : Forge.File.Time
Description : File time utilities

Provides utilities for working with file timestamps including
creation time, modification time, and access time.

== Coeffect Equation

@
  getFileTimes : String -> Graded Filesystem FileTime
  touch        : String -> Graded Filesystem Unit
@
-}
module Forge.File.Time
  ( -- * Types
    FileTime
    -- * Operations
  , getFileTimes
  , getModifiedTime
  , touch
  ) where

import Prelude

import Data.Either (Either(..))
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | File time info in milliseconds since Unix epoch
type FileTime =
  { created :: Number   -- birthtime
  , modified :: Number  -- mtime
  , accessed :: Number  -- atime
  }

-- ============================================================================
-- FFI
-- ============================================================================

-- | Get file stats via FFI
foreign import getFileStatsFFI :: String -> Aff (Either String FileTime)

-- | Touch a file via FFI
foreign import touchFileFFI :: String -> Aff (Either String Unit)

-- ============================================================================
-- OPERATIONS
-- ============================================================================

{-| Get file timestamps.

Returns creation, modification, and access times for a file.
-}
getFileTimes :: String -> Aff (Either String FileTime)
getFileTimes = getFileStatsFFI

{-| Get just the modified time.

Convenience function for common use case.
-}
getModifiedTime :: String -> Aff (Either String Number)
getModifiedTime path = do
  result <- getFileTimes path
  pure $ case result of
    Left err -> Left err
    Right times -> Right times.modified

{-| Touch a file (update modified time).

Updates the file's modification and access times to the current time.
Creates the file if it doesn't exist.
-}
touch :: String -> Aff (Either String Unit)
touch = touchFileFFI
