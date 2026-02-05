-- | Test Fixtures - Proper test data without unsafeCoerce
-- |
-- | **Purpose:** Provides test fixtures for all types used in tests.
-- |             Replaces unsafeCoerce with proper constructors.
module Test.Sidepanel.TestFixtures where

import Prelude
import Data.DateTime (DateTime, Date, Time, adjust)
import Data.Date (exactDate)
import Data.Time (hour, minute, second, millisecond)
import Data.Time.Component (Hour, Minute, Second, Millisecond)
import Data.Enum (toEnum)
import Data.Maybe (fromJust)
import Partial.Unsafe (unsafePartial)

-- | Create a test DateTime for January 1, 2024 at 12:00:00 UTC
testDateTime :: DateTime
testDateTime = unsafePartial $ fromJust $ do
  date <- exactDate 2024 bottom bottom
  hour <- toEnum 12 :: Maybe Hour
  minute <- toEnum 0 :: Maybe Minute
  second <- toEnum 0 :: Maybe Second
  millisecond <- toEnum 0 :: Maybe Millisecond
  pure $ DateTime date (Time hour minute second millisecond)

-- | Create a test DateTime for a specific date/time
createTestDateTime :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> DateTime
createTestDateTime year month day h m s ms = unsafePartial $ fromJust $ do
  date <- exactDate year month day
  hour <- toEnum h :: Maybe Hour
  minute <- toEnum m :: Maybe Minute
  second <- toEnum s :: Maybe Second
  millisecond <- toEnum ms :: Maybe Millisecond
  pure $ DateTime date (Time hour minute second millisecond)

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
