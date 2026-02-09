-- | Filesystem utilities
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/filesystem.ts
module Forge.Util.Filesystem
  ( exists
  , isDir
  , normalizePath
  , overlaps
  , contains
  , findUp
  , up
  , globUp
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Maybe (Maybe)

-- | Check if path exists
foreign import exists :: String -> Aff Boolean

-- | Check if path is a directory
foreign import isDir :: String -> Aff Boolean

-- | Normalize path casing (Windows-specific)
foreign import normalizePath :: String -> String

-- | Check if two paths overlap
foreign import overlaps :: String -> String -> Boolean

-- | Check if parent contains child
foreign import contains :: String -> String -> Boolean

-- | Find target file upward from start directory
foreign import findUp :: String -> String -> Maybe String -> Aff (Array String)

-- | Async generator for iterating up directories
-- | Returns paths matching targets going up from start
foreign import up :: { targets :: Array String, start :: String, stop :: Maybe String } -> Aff (Array String)

-- | Glob pattern search going up directories
foreign import globUp :: String -> String -> Maybe String -> Aff (Array String)
