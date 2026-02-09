{-|
Module      : Forge.File.Watcher
Description : File system watcher

Watches directories for file changes and emits events for
created, modified, and deleted files.

== Coeffect Equation

@
  watch : String -> (WatchEvent -> Effect Unit) -> Graded Filesystem Watcher
@

== Events

The watcher emits three types of events:
- Created: A new file was created
- Modified: An existing file was changed
- Deleted: A file was removed
-}
module Forge.File.Watcher
  ( -- * Types
    WatchEventType(..)
  , WatchEvent
  , Watcher
  , WatchOptions
    -- * Operations
  , watch
  , watchWithOptions
  , close
    -- * Default Options
  , defaultOptions
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Watch event type
data WatchEventType 
  = Created 
  | Modified 
  | Deleted
  | Renamed

derive instance eqWatchEventType :: Eq WatchEventType

instance showWatchEventType :: Show WatchEventType where
  show Created = "created"
  show Modified = "modified"
  show Deleted = "deleted"
  show Renamed = "renamed"

-- | Watch event
type WatchEvent =
  { eventType :: WatchEventType
  , path :: String
  , oldPath :: Maybe String  -- For rename events
  }

-- | Watcher instance handle
type Watcher =
  { close :: Effect Unit
  , path :: String
  }

-- | Watch options
type WatchOptions =
  { recursive :: Boolean      -- Watch subdirectories
  , persistent :: Boolean     -- Keep process running
  , ignoreInitial :: Boolean  -- Don't emit for existing files
  , ignored :: Array String   -- Patterns to ignore
  , depth :: Maybe Int        -- Max directory depth
  , debounceMs :: Int         -- Debounce time in ms
  }

-- ============================================================================
-- FFI
-- ============================================================================

-- | Start watching via FFI
foreign import watchDirectoryFFI :: 
  String -> 
  WatchOptions -> 
  (String -> String -> Maybe String -> Effect Unit) -> 
  Aff (Either String { close :: Effect Unit })

-- ============================================================================
-- OPERATIONS
-- ============================================================================

-- | Default watch options
defaultOptions :: WatchOptions
defaultOptions =
  { recursive: true
  , persistent: true
  , ignoreInitial: true
  , ignored: ["node_modules", ".git", "dist", "build"]
  , depth: Nothing
  , debounceMs: 100
  }

{-| Watch a directory for changes.

Uses default options. For custom options, use watchWithOptions.
-}
watch :: String -> (WatchEvent -> Effect Unit) -> Aff (Either String Watcher)
watch path handler = watchWithOptions path defaultOptions handler

{-| Watch a directory with custom options. -}
watchWithOptions :: String -> WatchOptions -> (WatchEvent -> Effect Unit) -> Aff (Either String Watcher)
watchWithOptions path options handler = do
  result <- watchDirectoryFFI path options wrappedHandler
  case result of
    Left err -> pure $ Left err
    Right watcher -> pure $ Right { close: watcher.close, path }
  where
    wrappedHandler :: String -> String -> Maybe String -> Effect Unit
    wrappedHandler eventTypeStr filePath oldPath = do
      let eventType = parseEventType eventTypeStr
      handler { eventType, path: filePath, oldPath }
    
    parseEventType :: String -> WatchEventType
    parseEventType "add" = Created
    parseEventType "change" = Modified
    parseEventType "unlink" = Deleted
    parseEventType "rename" = Renamed
    parseEventType _ = Modified  -- Default to modified

{-| Close a watcher. -}
close :: Watcher -> Effect Unit
close watcher = watcher.close
