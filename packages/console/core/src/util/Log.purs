-- | Log Utility Module
-- |
-- | Provides structured logging with tags and context.
-- | Pure functional logging that accumulates entries.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/util/log.ts
module Forge.Console.Core.Util.Log
  ( Logger
  , LogLevel(..)
  , LogEntry
  , create
  , tag
  , info
  , warn
  , error_
  , debug
  , getEntries
  ) where

import Prelude

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map

-- | Log levels
data LogLevel
  = Debug
  | Info
  | Warn
  | Error

derive instance eqLogLevel :: Eq LogLevel
derive instance ordLogLevel :: Ord LogLevel

instance showLogLevel :: Show LogLevel where
  show Debug = "debug"
  show Info = "info"
  show Warn = "warn"
  show Error = "error"

-- | A log entry
type LogEntry =
  { level :: LogLevel
  , message :: String
  , tags :: Map String String
  }

-- | Logger accumulates log entries (pure, no side effects)
type Logger =
  { tags :: Map String String
  , entries :: Array LogEntry
  }

-- | Create a new logger
create :: Logger
create = { tags: Map.empty, entries: [] }

-- | Add a tag to the logger
tag :: String -> String -> Logger -> Logger
tag key value logger = 
  logger { tags = Map.insert key value logger.tags }

-- | Log at info level
info :: String -> Logger -> Logger
info message logger = 
  logger { entries = Array.snoc logger.entries 
    { level: Info, message, tags: logger.tags } 
  }

-- | Log at warn level
warn :: String -> Logger -> Logger
warn message logger = 
  logger { entries = Array.snoc logger.entries 
    { level: Warn, message, tags: logger.tags } 
  }

-- | Log at error level
error_ :: String -> Logger -> Logger
error_ message logger = 
  logger { entries = Array.snoc logger.entries 
    { level: Error, message, tags: logger.tags } 
  }

-- | Log at debug level
debug :: String -> Logger -> Logger
debug message logger = 
  logger { entries = Array.snoc logger.entries 
    { level: Debug, message, tags: logger.tags } 
  }

-- | Get all log entries
getEntries :: Logger -> Array LogEntry
getEntries logger = logger.entries
