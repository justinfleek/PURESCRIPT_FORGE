-- | ACP Types
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/acp/types.ts
module Opencode.ACP.Types where

import Prelude
import Data.Maybe (Maybe)

-- | ACP Message
type ACPMessage =
  { id :: String
  , type :: String
  , payload :: String
  }

-- | ACP Request
type ACPRequest =
  { method :: String
  , params :: Maybe String
  }

-- | ACP Response
type ACPResponse =
  { result :: Maybe String
  , error :: Maybe ACPError
  }

-- | ACP Error
type ACPError =
  { code :: Int
  , message :: String
  }
