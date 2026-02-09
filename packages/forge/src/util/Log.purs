-- | Logging utilities
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/log.ts
module Forge.Util.Log
  ( Level(..)
  , Logger
  , Options
  , init
  , create
  , file
  , defaultLogger
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- | Log level
data Level = DEBUG | INFO | WARN | ERROR

-- | Logger options
type Options =
  { print :: Boolean
  , dev :: Maybe Boolean
  , level :: Maybe Level
  }

-- | Logger instance (using Foreign to break type cycle)
type Logger = Foreign

-- | Initialize logging
foreign import init :: Options -> Aff Unit

-- | Get log file path
foreign import file :: Effect String

-- | Create a logger with tags
foreign import create :: forall r. { | r } -> Logger

-- | Default logger
foreign import defaultLogger :: Logger
