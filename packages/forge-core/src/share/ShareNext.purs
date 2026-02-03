-- | Session Sharing (Next version)
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/share/share-next.ts
module Forge.Share.ShareNext where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | Share options
type ShareOptions =
  { visibility :: String  -- "public" | "private"
  , expiresIn :: Maybe Int
  }

-- | Share a session with options
shareWithOptions :: String -> ShareOptions -> Aff (Either String String)
shareWithOptions sessionId options = notImplemented "Share.ShareNext.shareWithOptions"
