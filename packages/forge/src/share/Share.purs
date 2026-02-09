-- | Session Sharing
-- | 1:1 parity with opencode-dev/packages/opencode/src/share/share.ts
module Forge.Share.Share where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)

type ShareInfo =
  { url :: String
  , expiresAt :: Maybe Number
  }

foreign import shareImpl :: String -> Aff (Either String ShareInfo)
foreign import unshareImpl :: String -> Aff (Either String Unit)

share :: String -> Aff (Either String ShareInfo)
share sessionId = shareImpl sessionId

unshare :: String -> Aff (Either String Unit)
unshare sessionId = unshareImpl sessionId
