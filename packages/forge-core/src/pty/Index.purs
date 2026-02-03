-- | PTY (Pseudo Terminal)
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/pty/index.ts
module Forge.PTY.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | PTY configuration
type PTYConfig =
  { shell :: Maybe String
  , cwd :: Maybe String
  , cols :: Int
  , rows :: Int
  }

-- | PTY instance
type PTY =
  { id :: String
  , config :: PTYConfig
  }

-- | Spawn a PTY
spawn :: PTYConfig -> Aff (Either String PTY)
spawn config = notImplemented "PTY.Index.spawn"

-- | Write to PTY
write :: String -> String -> Aff (Either String Unit)
write ptyId data_ = notImplemented "PTY.Index.write"

-- | Resize PTY
resize :: String -> Int -> Int -> Aff (Either String Unit)
resize ptyId cols rows = notImplemented "PTY.Index.resize"

-- | Kill PTY
kill :: String -> Aff (Either String Unit)
kill ptyId = notImplemented "PTY.Index.kill"
