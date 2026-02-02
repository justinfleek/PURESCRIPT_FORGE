-- | Session Sharing (Next version)
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/share/share-next.ts
module Opencode.Share.ShareNext where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Share options
type ShareOptions =
  { visibility :: String  -- "public" | "private"
  , expiresIn :: Maybe Int
  }

-- | Share a session with options
shareWithOptions :: String -> ShareOptions -> Aff (Either String String)
shareWithOptions sessionId options = notImplemented "Share.ShareNext.shareWithOptions"
