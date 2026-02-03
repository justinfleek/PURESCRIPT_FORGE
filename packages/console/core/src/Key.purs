-- | Key Module
-- |
-- | API key management operations.
-- | Keys are used for API authentication and belong to users.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/key.ts
module Forge.Console.Core.Key
  ( list
  , create
  , remove
  , CreateInput
  , RemoveInput
  , KeyInfo
  , generateSecretKey
  , maskKey
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.CodeUnits as CU
import Forge.Console.Core.Identifier as Identifier
import Forge.Console.Core.Schema.Key (KeyId, SecretKey)
import Forge.Console.Core.Schema.User (UserId)
import Forge.Console.Core.Actor (ActorInfo(..), UserRole(..))

-- | Key info returned from list
type KeyInfo =
  { id :: KeyId
  , name :: String
  , key :: Maybe SecretKey
  , keyDisplay :: String
  , userID :: UserId
  , email :: String
  }

-- | Input for creating a key
type CreateInput =
  { userID :: UserId
  , name :: String
  , randomBytes :: Array Int
  , timestamp :: Int
  }

-- | Input for removing a key
type RemoveInput =
  { id :: KeyId
  , actor :: ActorInfo
  }

-- | Character set for key generation
keyChars :: String
keyChars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"

-- | Generate a secret key from random bytes
-- | Format: sk-{64 chars}
generateSecretKey :: Array Int -> SecretKey
generateSecretKey randoms =
  let 
    chars = Array.take 64 randoms
    encoded = map encodeChar chars
    keyBody = String.joinWith "" encoded
  in "sk-" <> keyBody
  where
    encodeChar :: Int -> String
    encodeChar n = 
      let idx = n `mod` 62
      in case CU.charAt idx keyChars of
        Just c -> CU.singleton c
        Nothing -> "A"

-- | Mask a key for display
-- | Shows first 7 and last 4 characters
maskKey :: SecretKey -> String
maskKey key = 
  let 
    prefix = String.take 7 key
    suffix = String.takeRight 4 key
  in prefix <> "..." <> suffix

-- | List keys (pure representation)
list :: ActorInfo -> { table :: String, isAdmin :: Boolean }
list actor = 
  case actor of
    User u -> { table: "key", isAdmin: u.role == Admin }
    _ -> { table: "key", isAdmin: false }

-- | Create a new API key
create :: CreateInput -> Either String { keyId :: KeyId, secretKey :: SecretKey }
create input =
  let 
    keyId = Identifier.toString $ Identifier.create Identifier.Key
      { timestamp: input.timestamp, random: input.randomBytes }
    secretKey = generateSecretKey input.randomBytes
  in Right { keyId, secretKey }

-- | Remove a key
remove :: RemoveInput -> Either String Unit
remove input = 
  case input.actor of
    User _ -> Right unit
    _ -> Left "Only user actors can remove keys"
