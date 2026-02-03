-- | PureScript type definitions for Forge Session Status types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript/Zod types from forge-dev/packages/forge/src/session/status.ts
module Forge.Types.SessionStatus where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, (.:), (.:?))

-- | Session status type
data SessionStatus
  = Idle
  | Retry { attempt :: Int, message :: String, next :: Number }
  | Busy

derive instance genericSessionStatus :: Generic SessionStatus _
derive instance eqSessionStatus :: Eq SessionStatus

instance showSessionStatus :: Show SessionStatus where
  show = genericShow

instance encodeJsonSessionStatus :: EncodeJson SessionStatus where
  encodeJson = case _ of
    Idle -> encodeJson { type: "idle" }
    Retry r -> encodeJson { type: "retry", attempt: r.attempt, message: r.message, next: r.next }
    Busy -> encodeJson { type: "busy" }

instance decodeJsonSessionStatus :: DecodeJson SessionStatus where
  decodeJson json = do
    obj <- decodeJson json
    type_ <- obj .: "type"
    case type_ of
      "idle" -> pure Idle
      "retry" -> do
        attempt <- obj .: "attempt"
        message <- obj .: "message"
        next <- obj .: "next"
        pure $ Retry { attempt, message, next }
      "busy" -> pure Busy
      _ -> Left "Invalid session status type"

-- | Session status information
type SessionStatusInfo =
  { sessionID :: String
  , status :: SessionStatus
  }

derive instance genericSessionStatusInfo :: Generic SessionStatusInfo _
derive instance eqSessionStatusInfo :: Eq SessionStatusInfo

instance showSessionStatusInfo :: Show SessionStatusInfo where
  show = genericShow
