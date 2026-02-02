-- | Session Sharing
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/share/share.ts
module Opencode.Share.Share where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Share info
type ShareInfo =
  { url :: String
  , expiresAt :: Maybe Number
  }

-- | Share a session
share :: String -> Aff (Either String ShareInfo)
share sessionId = notImplemented "Share.Share.share"

-- | Unshare a session
unshare :: String -> Aff (Either String Unit)
unshare sessionId = notImplemented "Share.Share.unshare"
