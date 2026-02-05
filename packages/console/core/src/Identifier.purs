-- | Identifier Module
-- |
-- | Generates unique identifiers with entity-type prefixes.
-- | Uses Crockford Base32 encoding for sortable, URL-safe IDs.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/identifier.ts
module Forge.Console.Core.Identifier
  ( EntityType(..)
  , Prefix
  , Identifier(..)
  , AccountId
  , UserId
  , WorkspaceId
  , create
  , fromString
  , validate
  , getPrefix
  , allPrefixes
  , toString
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.CodeUnits as CU

-- | Entity types with their corresponding prefixes
data EntityType
  = Account     -- acc
  | Auth        -- aut
  | Benchmark   -- ben
  | Billing     -- bil
  | Key         -- key
  | Model       -- mod
  | Payment     -- pay
  | Provider    -- prv
  | Subscription -- sub
  | Usage       -- usg
  | User        -- usr
  | Workspace   -- wrk

derive instance eqEntityType :: Eq EntityType

instance showEntityType :: Show EntityType where
  show Account = "account"
  show Auth = "auth"
  show Benchmark = "benchmark"
  show Billing = "billing"
  show Key = "key"
  show Model = "model"
  show Payment = "payment"
  show Provider = "provider"
  show Subscription = "subscription"
  show Usage = "usage"
  show User = "user"
  show Workspace = "workspace"

-- | Prefix type alias
type Prefix = String

-- | Identifier newtype for type-safe IDs
newtype Identifier = Identifier String

derive instance eqIdentifier :: Eq Identifier

instance showIdentifier :: Show Identifier where
  show (Identifier s) = s

-- | Get the prefix for an entity type
getPrefix :: EntityType -> Prefix
getPrefix Account = "acc"
getPrefix Auth = "aut"
getPrefix Benchmark = "ben"
getPrefix Billing = "bil"
getPrefix Key = "key"
getPrefix Model = "mod"
getPrefix Payment = "pay"
getPrefix Provider = "prv"
getPrefix Subscription = "sub"
getPrefix Usage = "usg"
getPrefix User = "usr"
getPrefix Workspace = "wrk"

-- | All prefixes for validation
allPrefixes :: Array { entityType :: EntityType, prefix :: Prefix }
allPrefixes =
  [ { entityType: Account, prefix: "acc" }
  , { entityType: Auth, prefix: "aut" }
  , { entityType: Benchmark, prefix: "ben" }
  , { entityType: Billing, prefix: "bil" }
  , { entityType: Key, prefix: "key" }
  , { entityType: Model, prefix: "mod" }
  , { entityType: Payment, prefix: "pay" }
  , { entityType: Provider, prefix: "prv" }
  , { entityType: Subscription, prefix: "sub" }
  , { entityType: Usage, prefix: "usg" }
  , { entityType: User, prefix: "usr" }
  , { entityType: Workspace, prefix: "wrk" }
  ]

-- | Crockford Base32 alphabet for ULID encoding
base32Alphabet :: String
base32Alphabet = "0123456789ABCDEFGHJKMNPQRSTVWXYZ"

-- | Create a new identifier for the given entity type
-- | Takes a timestamp and random component for deterministic generation
-- | Format: {prefix}_{26 base32 chars}
create :: EntityType -> { timestamp :: Int, random :: Array Int } -> Identifier
create entityType { timestamp, random } =
  let 
    prefix = getPrefix entityType
    -- Encode timestamp (10 chars) and random (16 chars) to base32
    encoded = encodeTimestamp timestamp <> encodeRandom random
  in Identifier $ prefix <> "_" <> encoded

-- | Encode timestamp to 10 base32 characters
encodeTimestamp :: Int -> String
encodeTimestamp ts = 
  let 
    encode n acc count
      | count >= 10 = acc
      | otherwise = 
          let 
            char = CU.charAt (n `mod` 32) base32Alphabet
            charStr = case char of
              Just c -> CU.singleton c
              Nothing -> "0"
          in encode (n / 32) (charStr <> acc) (count + 1)
  in encode ts "" 0

-- | Encode random bytes to 16 base32 characters
encodeRandom :: Array Int -> String
encodeRandom randoms =
  String.joinWith "" $ map encodeRandomByte (Array.take 16 randoms)
  where
    encodeRandomByte :: Int -> String
    encodeRandomByte n = 
      case CU.charAt (n `mod` 32) base32Alphabet of
        Just c -> CU.singleton c
        Nothing -> "0"

-- | Validate that an ID has the correct prefix for its entity type
validate :: EntityType -> String -> Either String Identifier
validate entityType id =
  let 
    prefix = getPrefix entityType
    expectedPrefix = prefix <> "_"
  in if String.take 4 id == expectedPrefix
       then Right (Identifier id)
       else Left $ "ID " <> id <> " does not start with " <> expectedPrefix

-- | Convert identifier to string
toString :: Identifier -> String
toString (Identifier s) = s

-- | Create identifier from a raw string
-- | No validation - assumes the string is a valid identifier
fromString :: String -> Identifier
fromString = Identifier

-- | Type aliases for common entity IDs
type AccountId = String
type UserId = String
type WorkspaceId = String
