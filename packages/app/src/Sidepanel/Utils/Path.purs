-- | Path manipulation utilities
module Sidepanel.Utils.Path
  ( getFilename
  ) where

import Prelude
import Data.Array (last)
import Data.Maybe (fromMaybe)
import Data.String (split, Pattern(..))

-- | Extract the filename (last path segment) from a full path.
-- | e.g. "/home/user/project" -> "project"
-- |       "C:\\Users\\project" -> "project"
getFilename :: String -> String
getFilename path =
  let
    forwardSegments = split (Pattern "/") path
    -- If there's only one segment, try backslash split
    segments = case forwardSegments of
      [single] -> split (Pattern "\\") single
      other -> other
  in
    fromMaybe path (last segments)
