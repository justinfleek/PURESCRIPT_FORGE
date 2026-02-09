-- | Time Utilities
-- | Time calculation and formatting utilities
module Bridge.Utils.Time where

import Prelude
import Effect (Effect)
import Data.DateTime (DateTime)
import Data.Maybe (Maybe(..))

-- | Calculate time remaining until target
calculateTimeRemaining :: DateTime -> DateTime -> Maybe { hours :: Int, minutes :: Int, seconds :: Int, totalMs :: Number }
calculateTimeRemaining now target = 
  let diff = diffDateTime target now
  in if diff.totalMs <= 0.0 then
      Nothing
    else
      Just diff

-- | Format time remaining as string
formatTimeRemaining :: { hours :: Int, minutes :: Int, seconds :: Int, totalMs :: Number } -> String
formatTimeRemaining remaining =
  padZero remaining.hours <> "h " <>
  padZero remaining.minutes <> "m " <>
  padZero remaining.seconds <> "s"

-- | Format time remaining compact
formatTimeRemainingCompact :: { hours :: Int, minutes :: Int, seconds :: Int, totalMs :: Number } -> String
formatTimeRemainingCompact remaining =
  show remaining.hours <> ":" <>
  padZero remaining.minutes <> ":" <>
  padZero remaining.seconds

-- | Pad number with zero
padZero :: Int -> String
padZero n = 
  if n < 10 then
    "0" <> show n
  else
    show n

foreign import diffDateTime :: DateTime -> DateTime -> { hours :: Int, minutes :: Int, seconds :: Int, totalMs :: Number }
foreign import getCurrentDateTime :: Effect DateTime
