-- | PureScript type definitions for Forge Session Status types
-- | Phase 2: Type Safety Layer
module Forge.Types.SessionStatus where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Either (Either(..))
import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, (.:))
import Data.Argonaut.Decode.Error (JsonDecodeError(..))

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
    Idle -> encodeJson { statusType: "idle" }
    Retry r -> encodeJson { statusType: "retry", attempt: r.attempt, message: r.message, next: r.next }
    Busy -> encodeJson { statusType: "busy" }

instance decodeJsonSessionStatus :: DecodeJson SessionStatus where
  decodeJson json = do
    obj <- decodeJson json
    statusType <- obj .: "statusType"
    case statusType of
      "idle" -> pure Idle
      "retry" -> do
        attempt <- obj .: "attempt"
        message <- obj .: "message"
        next <- obj .: "next"
        pure $ Retry { attempt, message, next }
      "busy" -> pure Busy
      _ -> Left (UnexpectedValue json)

-- | Session status information
type SessionStatusInfo =
  { sessionID :: String
  , status :: SessionStatus
  }
