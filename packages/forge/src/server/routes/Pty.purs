-- | PTY route
-- | 1:1 parity with opencode-dev/packages/opencode/src/server/routes/pty.ts
module Forge.Server.Routes.Pty where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)

-- | Create a new PTY session
create :: Aff (Either String String)
create = createFFI

-- | Write to a PTY session
write :: String -> String -> Aff (Either String Unit)
write sessionID dat = writeFFI sessionID dat

-- | Resize a PTY session
resize :: String -> Int -> Int -> Aff (Either String Unit)
resize sessionID cols rows = resizeFFI sessionID cols rows

-- | Close a PTY session
close :: String -> Aff (Either String Unit)
close sessionID = closeFFI sessionID

foreign import createFFI :: Aff (Either String String)
foreign import writeFFI :: String -> String -> Aff (Either String Unit)
foreign import resizeFFI :: String -> Int -> Int -> Aff (Either String Unit)
foreign import closeFFI :: String -> Aff (Either String Unit)
