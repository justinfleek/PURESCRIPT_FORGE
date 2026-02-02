-- | Ripgrep integration
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/file/ripgrep.ts
module Opencode.File.Ripgrep where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Ripgrep search options
type RipgrepOptions =
  { pattern :: String
  , path :: String
  , include :: Maybe String
  , maxResults :: Maybe Int
  }

-- | Ripgrep match
type RipgrepMatch =
  { file :: String
  , line :: Int
  , column :: Int
  , text :: String
  }

-- | Search using ripgrep
search :: RipgrepOptions -> Aff (Either String (Array RipgrepMatch))
search options = notImplemented "File.Ripgrep.search"

-- | Check if ripgrep is available
isAvailable :: Aff Boolean
isAvailable = notImplemented "File.Ripgrep.isAvailable"
