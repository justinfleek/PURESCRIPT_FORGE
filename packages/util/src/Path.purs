-- | Path utilities
-- | Migrated from opencode-dev/packages/util/src/path.ts
module Opencode.Util.Path
  ( getFilename
  , getDirectory
  , getFileExtension
  , getFilenameTruncated
  , truncateMiddle
  ) where

import Prelude
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), split, length, take, drop, lastIndexOf)
import Data.String.Regex (regex, replace)
import Data.String.Regex.Flags (global)
import Data.Array (last, init)
import Data.Either (hush)

-- | Get filename from path
getFilename :: Maybe String -> String
getFilename Nothing = ""
getFilename (Just path) =
  let trimmed = trimTrailingSlash path
      parts = split (Pattern "/") trimmed
  in fromMaybe "" (last parts)

-- | Get directory from path
getDirectory :: Maybe String -> String
getDirectory Nothing = ""
getDirectory (Just path) =
  let trimmed = trimTrailingSlash path
      parts = split (Pattern "/") trimmed
  in case init parts of
    Nothing -> "/"
    Just dirs -> intercalate "/" dirs <> "/"

-- | Get file extension
getFileExtension :: Maybe String -> String
getFileExtension Nothing = ""
getFileExtension (Just path) =
  let parts = split (Pattern ".") path
  in fromMaybe "" (last parts)

-- | Get truncated filename with extension preserved
getFilenameTruncated :: Maybe String -> Int -> String
getFilenameTruncated path maxLen =
  let filename = getFilename path
  in if length filename <= maxLen
    then filename
    else case lastIndexOf (Pattern ".") filename of
      Nothing -> take (maxLen - 1) filename <> "..."
      Just dotIdx ->
        let ext = drop dotIdx filename
            available = maxLen - length ext - 1
        in if available <= 0
          then take (maxLen - 1) filename <> "..."
          else take available filename <> "..." <> ext

-- | Truncate string in the middle
truncateMiddle :: String -> Int -> String
truncateMiddle text maxLen
  | length text <= maxLen = text
  | otherwise =
      let available = maxLen - 1
          startLen = (available + 1) / 2
          endLen = available / 2
      in take startLen text <> "..." <> drop (length text - endLen) text

-- Helpers
trimTrailingSlash :: String -> String
trimTrailingSlash s = fromMaybe s do
  r <- hush (regex "[\\/\\\\]+$" global)
  pure (replace r "" s)

intercalate :: String -> Array String -> String
intercalate sep arr = case arr of
  [] -> ""
  _ -> foldl (\acc x -> if acc == "" then x else acc <> sep <> x) "" arr
  where
  foldl f z xs = case xs of
    [] -> z
    [x] -> f z x
    _ -> foldl f (f z (fromMaybe "" (head xs))) (fromMaybe [] (tail xs))
  head xs = xs !! 0
  tail xs = drop 1 xs
