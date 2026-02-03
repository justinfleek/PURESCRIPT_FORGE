-- | Monotonic ID generation
-- | Migrated from forge-dev/packages/util/src/identifier.ts
module Forge.Util.Identifier
  ( ascending
  , descending
  , create
  ) where

import Prelude
import Effect (Effect)
import Effect.Now (now)
import Effect.Random (randomInt)
import Effect.Ref (Ref, new, read, write)
import Effect.Unsafe (unsafePerformEffect)
import Data.DateTime.Instant (unInstant)
import Data.Time.Duration (Milliseconds(..))
import Data.Int (toStringAs, hexadecimal)
import Data.String (length) as String
import Data.Array (replicate)
import Data.String.CodeUnits (fromCharArray)

-- Module state for monotonic generation
lastTimestamp :: Ref Number
lastTimestamp = unsafePerformEffect (new 0.0)

counter :: Ref Int
counter = unsafePerformEffect (new 0)

-- | Generate ascending ID (newer = higher)
ascending :: Effect String
ascending = create false

-- | Generate descending ID (newer = lower)
descending :: Effect String
descending = create true

-- | Create a monotonic ID
create :: Boolean -> Effect String
create desc = do
  Milliseconds ms <- unInstant <$> now
  lastTs <- read lastTimestamp
  cnt <- read counter
  
  let newCnt = if ms /= lastTs then 0 else cnt + 1
  write ms lastTimestamp
  write newCnt counter
  
  let timestamp = ms * 4096.0 + (toNumber newCnt)
  let adjusted = if desc then negate timestamp else timestamp
  
  timeHex <- toHex adjusted
  randomPart <- randomBase62 14
  pure (timeHex <> randomPart)

-- Base62 charset
base62Chars :: String
base62Chars = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"

randomBase62 :: Int -> Effect String
randomBase62 len = do
  chars <- sequence (replicate len randomChar)
  pure (fromCharArray chars)
  where
  randomChar = do
    idx <- randomInt 0 61
    pure (charAt' idx base62Chars)

-- FFI helpers
foreign import toHex :: Number -> Effect String
foreign import charAt' :: Int -> String -> Char
foreign import toNumber :: Int -> Number
foreign import negate :: Number -> Number
