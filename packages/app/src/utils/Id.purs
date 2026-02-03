-- | Monotonic identifier generation
-- | Migrated from: forge-dev/packages/app/src/utils/id.ts (100 lines)
module Sidepanel.Utils.Id
  ( Identifier
  , Prefix(..)
  , ascending
  , descending
  , schema
  , prefixString
  ) where

import Prelude

import Data.BigInt (BigInt)
import Data.BigInt as BigInt
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Now (now)

-- | Identifier prefix types
data Prefix
  = Session
  | Message
  | Permission
  | User
  | Part
  | Pty

derive instance eqPrefix :: Eq Prefix

-- | Convert prefix to string representation
prefixString :: Prefix -> String
prefixString = case _ of
  Session -> "ses"
  Message -> "msg"
  Permission -> "per"
  User -> "usr"
  Part -> "prt"
  Pty -> "pty"

-- | ID length constant
idLength :: Int
idLength = 26

-- | Module-level state for monotonic generation
foreign import lastTimestamp :: Ref Number
foreign import counter :: Ref Int

-- | Namespace for identifier operations
type Identifier =
  { schema :: Prefix -> String -> Boolean
  , ascending :: Prefix -> Maybe String -> Effect String
  , descending :: Prefix -> Maybe String -> Effect String
  }

-- | Check if a string starts with the expected prefix
schema :: Prefix -> String -> Boolean
schema prefix value = String.take (String.length pfx) value == pfx
  where
    pfx = prefixString prefix

-- | Generate ascending ID (newer IDs sort after older)
ascending :: Prefix -> Maybe String -> Effect String
ascending prefix given = generateID prefix false given

-- | Generate descending ID (newer IDs sort before older)
descending :: Prefix -> Maybe String -> Effect String
descending prefix given = generateID prefix true given

-- | Internal: generate or validate ID
generateID :: Prefix -> Boolean -> Maybe String -> Effect String
generateID prefix isDescending given = case given of
  Nothing -> create prefix isDescending
  Just id ->
    if schema prefix id
    then pure id
    else throwError $ "ID " <> id <> " does not start with " <> prefixString prefix

-- | Create a new ID
create :: Prefix -> Boolean -> Effect String
create prefix isDescending = do
  timestamp <- now <#> toNumber
  lastTs <- Ref.read lastTimestamp
  cnt <- if timestamp /= lastTs
         then do
           Ref.write timestamp lastTimestamp
           Ref.write 0 counter
           pure 1
         else do
           Ref.modify (_ + 1) counter
  
  let timeValue = BigInt.fromNumber timestamp * BigInt.fromInt 0x1000 + BigInt.fromInt cnt
      finalValue = if isDescending then BigInt.not timeValue else timeValue
      timeBytes = encodeTimeBytes finalValue
      randomPart = randomBase62 (idLength - 12)
  
  pure $ prefixString prefix <> "_" <> bytesToHex timeBytes <> randomPart

-- | Encode timestamp to 6 bytes
encodeTimeBytes :: BigInt -> Array Int
encodeTimeBytes value =
  map (\i -> BigInt.toInt ((BigInt.shr value (40 - 8 * i)) `BigInt.and` BigInt.fromInt 0xff)) [0, 1, 2, 3, 4, 5]

-- | Convert bytes to hex string
bytesToHex :: Array Int -> String
bytesToHex bytes = String.joinWith "" $ map toHex bytes
  where
    toHex n = 
      let hex = toHexDigit (n / 16) <> toHexDigit (n `mod` 16)
      in hex
    toHexDigit d
      | d < 10 = String.singleton (toEnum (d + 48))  -- '0' = 48
      | otherwise = String.singleton (toEnum (d + 87)) -- 'a' - 10 = 87

-- | Generate random base62 string
foreign import randomBase62 :: Int -> String

-- | Foreign helpers
foreign import throwError :: forall a. String -> Effect a
foreign import toNumber :: forall a. a -> Number
foreign import toEnum :: Int -> Char
