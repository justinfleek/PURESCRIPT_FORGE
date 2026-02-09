-- | Session Sharing (Next version)
-- | 1:1 parity with opencode-dev/packages/opencode/src/share/share-next.ts
module Forge.Share.ShareNext where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)

type ShareOptions =
  { visibility :: String
  , expiresIn :: Maybe Int
  }

foreign import shareWithOptionsImpl :: String -> ShareOptions -> Aff (Either String String)

shareWithOptions :: String -> ShareOptions -> Aff (Either String String)
shareWithOptions sessionId options = shareWithOptionsImpl sessionId options
