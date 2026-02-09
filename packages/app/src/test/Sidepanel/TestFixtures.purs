-- | Test Fixtures - Proper test data without unsafeCoerce
-- |
-- | **Purpose:** Provides test fixtures for all types used in tests.
-- |             Replaces unsafeCoerce with proper constructors.
module Test.Sidepanel.TestFixtures where

import Prelude
import Data.DateTime (DateTime(..))
import Data.Date (canonicalDate)
import Data.Time (Time(..))
import Data.Enum (toEnum)
import Data.Maybe (Maybe(..), fromJust)
import Partial.Unsafe (unsafePartial)

-- | Create a test DateTime for January 1, 2024 at 12:00:00 UTC
testDateTime :: DateTime
testDateTime = unsafePartial $ fromJust $ do
  y <- toEnum 2024
  mo <- toEnum 1
  d <- toEnum 1
  h <- toEnum 12
  mi <- toEnum 0
  s <- toEnum 0
  ms <- toEnum 0
  pure $ DateTime (canonicalDate y mo d) (Time h mi s ms)

-- | Create a test DateTime for a specific date/time
createTestDateTime :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> DateTime
createTestDateTime year month day h m s ms = unsafePartial $ fromJust $ do
  y <- toEnum year
  mo <- toEnum month
  d <- toEnum day
  hr <- toEnum h
  mi <- toEnum m
  sc <- toEnum s
  msc <- toEnum ms
  pure $ DateTime (canonicalDate y mo d) (Time hr mi sc msc)

-- | Default test session state
defaultTestSession :: { id :: String, model :: String, promptTokens :: Int, completionTokens :: Int, totalTokens :: Int, cost :: Number, messageCount :: Int, startedAt :: DateTime }
defaultTestSession = 
  { id: "test_session_1"
  , model: "test_model"
  , promptTokens: 100
  , completionTokens: 50
  , totalTokens: 150
  , cost: 0.01
  , messageCount: 1
  , startedAt: testDateTime
  }
