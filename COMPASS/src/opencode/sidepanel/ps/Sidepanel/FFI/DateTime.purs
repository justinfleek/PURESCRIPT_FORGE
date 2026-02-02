-- | DateTime FFI Module - DateTime Operations and UTC Calculations
-- |
-- | **What:** Provides FFI bindings for DateTime operations, including UTC midnight
-- |         calculations, current time retrieval, and ISO 8601 string parsing/formatting.
-- | **Why:** Enables accurate time calculations for Venice Diem reset countdown and provides
-- |         consistent DateTime handling across the application.
-- | **How:** Uses foreign function imports to access JavaScript Date API and provides
-- |         PureScript-friendly DateTime types and operations.
-- |
-- | **Dependencies:** None (pure FFI bindings)
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.FFI.DateTime as DateTime
-- |
-- | -- Get current time
-- | now <- liftEffect DateTime.getCurrentDateTime
-- |
-- | -- Calculate milliseconds until UTC midnight
-- | nowMs <- liftEffect DateTime.getCurrentTimeMs
-- | msUntilMidnight <- DateTime.calculateMsUntilMidnightUTC nowMs
-- |
-- | -- Parse ISO string
-- | dt <- DateTime.fromISOString "2026-01-30T12:34:56.789Z"
-- |
-- | -- Format to ISO string
-- | isoStr <- DateTime.toISOString dt
-- | ```
module Sidepanel.FFI.DateTime where

import Prelude
import Effect (Effect)
import Data.DateTime (DateTime)

-- | Calculate milliseconds until next UTC midnight
foreign import calculateMsUntilMidnightUTC :: Number -> Number

-- | Get current time in milliseconds
foreign import getCurrentTimeMs :: Effect Number

-- | Get current DateTime (from milliseconds)
foreign import getCurrentDateTime :: Effect DateTime

-- | Convert timestamp (milliseconds) to DateTime
foreign import fromTimestamp :: Number -> DateTime

-- | Parse ISO 8601 DateTime string to DateTime
-- | Handles formats like: "2026-01-30T12:34:56.789Z", "2026-01-30T12:34:56Z", etc.
foreign import fromISOString :: String -> DateTime

-- | Format DateTime as ISO 8601 string
-- | Returns format: "YYYY-MM-DDTHH:mm:ss.sssZ"
foreign import toISOString :: DateTime -> String
