-- | Currency Formatting Utilities - Currency and Token Cost Formatting
-- |
-- | **What:** Provides formatting functions for currency values (Diem, FLK, USD) and token costs.
-- |         Handles display formatting with appropriate precision, units, and currency symbols.
-- | **Why:** Ensures consistent currency formatting across the application, handles edge cases
-- |         (e.g., Diem < 1.0 displayed as cents), and provides readable cost representations.
-- | **How:** Formats numbers with appropriate decimal places, adds currency symbols, handles
-- |         unit conversions (Diem to cents, cost per token to cost per 1k tokens).
-- |
-- | **Dependencies:**
-- | - `Data.Number.Format`: Number formatting utilities
-- | - `Data.Int`: Integer operations
-- |
-- | **Mathematical Foundation:**
-- | - **Diem Formatting:** If diem >= 1.0, display as "X.XX Diem". If < 1.0, display as
-- |   "XX¢" (cents = diem * 100).
-- | - **FLK Formatting:** Display as "X.XX FLK" (Fleek Token, always shows decimal places).
-- | - **Number Formatting:** Removes trailing ".00" for whole numbers, otherwise shows
-- |   2 decimal places.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Utils.Currency as Currency
-- |
-- | -- Format Diem balance
-- | Currency.formatDiem 123.45  -- "123.45 Diem"
-- | Currency.formatDiem 0.75    -- "75¢"
-- |
-- | -- Format FLK balance
-- | Currency.formatFLK 1000.50  -- "1000.50 FLK"
-- |
-- | -- Format USD
-- | Currency.formatUSD 99.99     -- "$99.99"
-- |
-- | -- Format consumption rate
-- | Currency.formatConsumptionRate 5.50  -- "$5.50/hr"
-- | ```
-- |
-- | Based on spec 11-DIEM-TRACKING.md, 13-TOKEN-USAGE-METRICS.md
module Sidepanel.Utils.Currency where

import Prelude
import Data.Int (floor)
import Data.Number.Format (toStringWith, fixed)

-- | Format Diem balance
formatDiem :: Number -> String
formatDiem diem = 
  if diem >= 1.0
    then formatNumber diem <> " Diem"
    else formatNumber (diem * 100.0) <> "¢"

-- | Format FLK (Fleek Token) balance
formatFLK :: Number -> String
formatFLK flk = 
  formatNumber flk <> " FLK"

-- | Format USD amount
formatUSD :: Number -> String
formatUSD usd = "$" <> formatNumber usd

-- | Format effective balance (Diem + FLK + USD)
formatEffective :: Number -> String
formatEffective effective = formatUSD effective

-- | Format number with 2 decimal places
formatNumber :: Number -> String
formatNumber n = 
  let rounded = toStringWith (fixed 2) n
      whole = toStringWith (fixed 0) n
  in if rounded == whole <> ".00"
       then whole
       else rounded

-- | Format cost per token
formatCostPerToken :: Number -> String
formatCostPerToken cost = "$" <> formatNumber (cost * 1000.0) <> " per 1k tokens"

-- | Format consumption rate (per hour)
formatConsumptionRate :: Number -> String
formatConsumptionRate rate = formatUSD rate <> "/hr"

-- | Format time to depletion
formatTimeToDepletion :: Number -> String
formatTimeToDepletion hours =
  if hours < 1.0
    then show (floor (hours * 60.0)) <> " minutes"
    else if hours < 24.0
      then formatNumber hours <> " hours"
      else formatNumber (hours / 24.0) <> " days"
