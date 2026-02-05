-- | Omega Sticky Provider Tracker
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/stickyProviderTracker.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Omega.Util.StickyProviderTracker
  ( StickyMode(..)
  , StickyConfig(..)
  , StickyKey(..)
  , isEnabled
  , buildKey
  , expirationTtl
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- | Sticky provider mode
data StickyMode
  = Strict   -- Must use same provider
  | Prefer   -- Prefer same provider but can switch

derive instance eqStickyMode :: Eq StickyMode

instance showStickyMode :: Show StickyMode where
  show Strict = "strict"
  show Prefer = "prefer"

-- | Parse sticky mode from string
parseStickyMode :: String -> Maybe StickyMode
parseStickyMode "strict" = Just Strict
parseStickyMode "prefer" = Just Prefer
parseStickyMode _ = Nothing

-- | Sticky provider configuration
type StickyConfig =
  { mode :: StickyMode
  , session :: String
  }

-- | Sticky key for KV storage
newtype StickyKey = StickyKey String

derive instance eqStickyKey :: Eq StickyKey

instance showStickyKey :: Show StickyKey where
  show (StickyKey k) = k

-- | Check if sticky tracking is enabled
isEnabled :: Maybe StickyMode -> String -> Boolean
isEnabled Nothing _ = false
isEnabled (Just _) "" = false  -- No session = disabled
isEnabled (Just _) _ = true

-- | Build sticky key from session
buildKey :: String -> StickyKey
buildKey session = StickyKey $ "sticky:" <> session

-- | Expiration TTL in seconds (24 hours)
expirationTtl :: Int
expirationTtl = 86400

-- | Sticky provider value
type StickyValue =
  { providerId :: String
  , timestamp :: Int
  }

-- | Build sticky value for storage
buildStickyValue :: String -> Int -> StickyValue
buildStickyValue providerId timestamp =
  { providerId
  , timestamp
  }

-- | Check if sticky value is valid (not expired)
isValid :: StickyValue -> Int -> Boolean
isValid value currentTimestamp =
  currentTimestamp - value.timestamp < expirationTtl

-- | Get provider from sticky value if valid
getProvider :: Maybe StickyValue -> Int -> Maybe String
getProvider Nothing _ = Nothing
getProvider (Just value) currentTimestamp =
  if isValid value currentTimestamp
    then Just value.providerId
    else Nothing

-- | Should update sticky (only if strict mode or no existing)
shouldUpdate :: StickyMode -> Maybe String -> Boolean
shouldUpdate Strict Nothing = true
shouldUpdate Strict (Just _) = false  -- Don't change in strict mode
shouldUpdate Prefer _ = true  -- Always update in prefer mode

-- | Update decision
type UpdateDecision =
  { shouldUpdate :: Boolean
  , reason :: String
  }

-- | Decide whether to update sticky provider
decideUpdate :: StickyConfig -> Maybe String -> String -> UpdateDecision
decideUpdate config existingProvider newProvider =
  case config.mode of
    Strict ->
      case existingProvider of
        Nothing ->
          { shouldUpdate: true
          , reason: "No existing provider, setting initial sticky"
          }
        Just existing ->
          if existing == newProvider
            then { shouldUpdate: false, reason: "Same provider, no update needed" }
            else { shouldUpdate: false, reason: "Strict mode, cannot change provider" }
    Prefer ->
      { shouldUpdate: true
      , reason: "Prefer mode, updating to latest provider"
      }
