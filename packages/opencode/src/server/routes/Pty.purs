-- | PTY route
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/server/routes/pty.ts
module Opencode.Server.Routes.Pty where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Create a PTY session
create :: Aff (Either String String)
create = notImplemented "Server.Routes.Pty.create"

-- | Write to PTY
write :: String -> String -> Aff (Either String Unit)
write ptyId data_ = notImplemented "Server.Routes.Pty.write"

-- | Resize PTY
resize :: String -> Int -> Int -> Aff (Either String Unit)
resize ptyId cols rows = notImplemented "Server.Routes.Pty.resize"
