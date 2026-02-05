-- | Format utilities
module Opencode.Util.Format where

import Prelude

-- | Format bytes to human readable
formatBytes :: Int -> String
formatBytes bytes
  | bytes < 1024 = show bytes <> " B"
  | bytes < 1048576 = show (bytes / 1024) <> " KB"
  | bytes < 1073741824 = show (bytes / 1048576) <> " MB"
  | otherwise = show (bytes / 1073741824) <> " GB"

-- | Format duration in milliseconds
formatDuration :: Int -> String
formatDuration ms
  | ms < 1000 = show ms <> "ms"
  | ms < 60000 = show (ms / 1000) <> "s"
  | otherwise = show (ms / 60000) <> "m"

-- | Truncate string with ellipsis
truncate :: Int -> String -> String
truncate maxLen str = 
  if String.length str <= maxLen
    then str
    else String.take (maxLen - 3) str <> "..."
