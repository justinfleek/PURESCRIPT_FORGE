{-|
Module      : Forge.CLI.Upgrade
Description : CLI Upgrade functionality

Handles version checking and upgrade functionality for the CLI.
-}
module Forge.CLI.Upgrade
  ( -- * Types
    VersionInfo
  , UpgradeResult(..)
    -- * Operations
  , checkForUpdates
  , performUpgrade
  , getCurrentVersion
  , compareVersions
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Version information
type VersionInfo =
  { current :: String
  , latest :: String
  , updateAvailable :: Boolean
  , releaseNotes :: Maybe String
  , releaseUrl :: Maybe String
  }

-- | Upgrade result
data UpgradeResult
  = UpgradeSuccess String       -- New version
  | UpgradeNotNeeded            -- Already at latest
  | UpgradeError String         -- Error message

derive instance eqUpgradeResult :: Eq UpgradeResult

instance showUpgradeResult :: Show UpgradeResult where
  show (UpgradeSuccess v) = "Upgraded to " <> v
  show UpgradeNotNeeded = "Already at latest version"
  show (UpgradeError e) = "Upgrade error: " <> e

-- ============================================================================
-- FFI
-- ============================================================================

-- | Fetch latest version from registry
foreign import fetchLatestVersionFFI :: String -> Aff (Either String { version :: String, notes :: Maybe String, url :: Maybe String })

-- | Execute upgrade command
foreign import executeUpgradeFFI :: String -> Aff (Either String Unit)

-- ============================================================================
-- OPERATIONS
-- ============================================================================

-- | Get current version
getCurrentVersion :: String
getCurrentVersion = "0.1.0"  -- In production, read from package

-- | Check for available updates
checkForUpdates :: Aff (Either String VersionInfo)
checkForUpdates = do
  let current = getCurrentVersion
  result <- fetchLatestVersionFFI "forge"
  case result of
    Left err -> pure $ Left err
    Right info -> 
      let updateAvailable = compareVersions info.version current == GT
      in pure $ Right
           { current
           , latest: info.version
           , updateAvailable
           , releaseNotes: info.notes
           , releaseUrl: info.url
           }

-- | Perform the upgrade to a specific version
performUpgrade :: String -> Aff (Either String Unit)
performUpgrade version = do
  -- Check if already at this version
  if version == getCurrentVersion
    then pure $ Right unit
    else executeUpgradeFFI version

-- | Compare two semantic versions
-- | Returns: GT if v1 > v2, LT if v1 < v2, EQ if equal
compareVersions :: String -> String -> Ordering
compareVersions v1 v2 =
  let parts1 = parseVersion v1
      parts2 = parseVersion v2
  in compareVersionParts parts1 parts2

-- | Parse version string into parts
parseVersion :: String -> Array Int
parseVersion v =
  v 
    # String.split (String.Pattern ".")
    # Array.mapMaybe parseIntMaybe

-- | Compare version parts
compareVersionParts :: Array Int -> Array Int -> Ordering
compareVersionParts p1 p2 =
  let len = max (Array.length p1) (Array.length p2)
      padded1 = pad len p1
      padded2 = pad len p2
  in go padded1 padded2
  where
    pad :: Int -> Array Int -> Array Int
    pad n arr = arr <> Array.replicate (n - Array.length arr) 0
    
    go :: Array Int -> Array Int -> Ordering
    go a b = case Array.uncons a, Array.uncons b of
      Nothing, Nothing -> EQ
      Just { head: h1, tail: t1 }, Just { head: h2, tail: t2 } ->
        case compare h1 h2 of
          EQ -> go t1 t2
          other -> other
      _, _ -> EQ

-- | Parse integer with Maybe result
parseIntMaybe :: String -> Maybe Int
parseIntMaybe s =
  let trimmed = String.trim s
  in if String.null trimmed
     then Nothing
     else case parseIntFFI trimmed of
       n | n >= 0 -> Just n
       _ -> Nothing

foreign import parseIntFFI :: String -> Int
