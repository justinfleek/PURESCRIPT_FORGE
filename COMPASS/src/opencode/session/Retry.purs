-- | Session Retry - retry failed operations
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/session/retry.ts
module Opencode.Session.Retry where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Retry configuration
type RetryConfig =
  { maxAttempts :: Int
  , backoffMs :: Int
  , maxBackoffMs :: Int
  }

-- | Default retry config
defaultRetryConfig :: RetryConfig
defaultRetryConfig =
  { maxAttempts: 3
  , backoffMs: 1000
  , maxBackoffMs: 30000
  }

-- | Retry a failed message
retryMessage :: String -> String -> Aff (Either String Unit)
retryMessage sessionId messageId = notImplemented "Session.Retry.retryMessage"

-- | Retry from a specific point
retryFrom :: String -> String -> Aff (Either String Unit)
retryFrom sessionId fromMessageId = notImplemented "Session.Retry.retryFrom"
