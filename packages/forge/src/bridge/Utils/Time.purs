-- | Time Utilities
module Bridge.Utils.Time where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe(..))

-- | Time remaining breakdown
type TimeRemaining =
  { hours :: Int
  , minutes :: Int
  , seconds :: Int
  , totalMs :: Number
  }

-- | FFI for datetime difference calculation
foreign import diffDateTime :: Number -> Number -> TimeRemaining

-- | FFI for getting current time as epoch milliseconds
foreign import getCurrentDateTime :: Effect Number

-- | Calculate time remaining between now and target
calculateTimeRemaining :: Number -> Number -> Maybe TimeRemaining
calculateTimeRemaining now target =
  if target <= now then Nothing
  else Just (diffDateTime now target)

-- | Format time remaining as "XXh YYm ZZs"
formatTimeRemaining :: TimeRemaining -> String
formatTimeRemaining tr =
  show tr.hours <> "h " <> show tr.minutes <> "m " <> show tr.seconds <> "s"

-- | Format time remaining as "X:YY:ZZ"
formatTimeRemainingCompact :: TimeRemaining -> String
formatTimeRemainingCompact tr =
  show tr.hours <> ":" <> padZero tr.minutes <> ":" <> padZero tr.seconds

-- | Pad single-digit number with leading zero
padZero :: Int -> String
padZero n =
  if n < 10 then "0" <> show n
  else show n
