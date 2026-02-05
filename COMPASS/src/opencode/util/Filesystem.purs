-- | Filesystem utilities
module Opencode.Util.Filesystem where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))

-- | Check if path exists
exists :: String -> Aff Boolean
exists path = do
  result <- statPath path
  pure $ case result of
    Left _ -> false
    Right _ -> true

-- | Check if path is a directory
isDirectory :: String -> Aff Boolean
isDirectory path = do
  result <- statPath path
  pure $ case result of
    Left _ -> false
    Right stats -> stats.isDirectory

-- | Check if path is a file
isFile :: String -> Aff Boolean
isFile path = do
  result <- statPath path
  pure $ case result of
    Left _ -> false
    Right stats -> not stats.isDirectory

-- | Get file size
getSize :: String -> Aff (Either String Int)
getSize path = do
  result <- statPath path
  pure $ case result of
    Left err -> Left err
    Right stats -> Right stats.size

-- | Read directory contents
readDir :: String -> Aff (Either String (Array String))
readDir path = readDirectory path

-- | Create directory recursively
mkdirp :: String -> Aff (Either String Unit)
mkdirp path = makeDirectoryRecursive path

-- | File stats
type FileStats =
  { isDirectory :: Boolean
  , size :: Int
  }

-- | Stat a path
foreign import statPath :: String -> Aff (Either String FileStats)

-- | Read directory
foreign import readDirectory :: String -> Aff (Either String (Array String))

-- | Create directory recursively
foreign import makeDirectoryRecursive :: String -> Aff (Either String Unit)
