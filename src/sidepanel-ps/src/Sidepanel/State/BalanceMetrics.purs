-- | Balance Metrics Calculation - Consumption Rate and Time to Depletion
-- |
-- | **What:** Calculates consumption rate and time-to-depletion from balance history snapshots.
-- |         Implements the algorithms from spec 11-DIEM-TRACKING.md.
-- | **Why:** Provides accurate consumption metrics for display and alerting. Consumption rate
-- |         is calculated from recent balance changes, and time-to-depletion projects when
-- |         balance will reach zero.
-- | **How:** Uses balance snapshot history to calculate weighted average consumption rate,
-- |         then projects depletion time from current balance and rate.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.FFI.DateTime`: DateTime operations
-- | - `Data.Array`: Array operations for history processing
-- |
-- | **Mathematical Foundation:**
-- | - **Consumption Rate:** `rate = diemDelta / timeDeltaHours` (Diem per hour)
-- |   Uses weighted average with recency bias (more recent = higher weight)
-- | - **Time to Depletion:** `hours = currentDiem / rate` (if rate > 0)
-- |   Returns `Nothing` if rate <= 0 (not depleting)
-- |
-- | Based on spec 11-DIEM-TRACKING.md
module Sidepanel.State.BalanceMetrics where

import Prelude

import Data.Array as Array
import Data.DateTime (DateTime)
import Data.Maybe (Maybe(..))
import Data.Ord (max)
import Sidepanel.FFI.DateTime (toTimestamp, fromTimestamp, getCurrentDateTime)
import Math (pow)

-- | Balance snapshot for history tracking
type BalanceSnapshot =
  { timestamp :: DateTime
  , diem :: Number
  , usd :: Number
  }

-- | Calculate consumption rate from balance history
-- |
-- | **Purpose:** Calculates Diem consumption rate (Diem per hour) from balance history.
-- |             Uses recent snapshots (last hour) if available, otherwise falls back
-- |             to weighted average of all history.
-- | **Parameters:**
-- | - `history`: Array of balance snapshots (should be sorted by timestamp)
-- | - `currentTime`: Current DateTime for filtering recent snapshots
-- | **Returns:** Consumption rate in Diem per hour (0.0 if cannot calculate)
-- | **Side Effects:** None (pure function)
-- |
-- | **Algorithm:**
-- | 1. Filter snapshots from last hour
-- | 2. If >= 2 recent snapshots: Calculate rate from first to last
-- | 3. Otherwise: Use weighted average of all history (recent = more weight)
-- |
-- | **Example:**
-- | ```purescript
-- | rate = calculateConsumptionRate history now
-- | ```
calculateConsumptionRate :: Array BalanceSnapshot -> DateTime -> Number
calculateConsumptionRate history currentTime =
  if Array.length history < 2 then
    0.0
  else
    let
      currentTimestamp = toTimestamp currentTime
      oneHourAgo = currentTimestamp - (60.0 * 60.0 * 1000.0)  -- 1 hour in milliseconds
      recentSnapshots = Array.filter (\s -> toTimestamp s.timestamp > oneHourAgo) history
    in
      if Array.length recentSnapshots >= 2 then
        calculateRecentRate recentSnapshots
      else
        calculateLongTermRate history

-- | Calculate rate from recent snapshots (last hour)
calculateRecentRate :: Array BalanceSnapshot -> Number
calculateRecentRate snapshots =
  let
    sorted = Array.sortBy (\a b -> compare (toTimestamp a.timestamp) (toTimestamp b.timestamp)) snapshots
    first = Array.head sorted
    last = Array.last sorted
  in
    case first, last of
      Just f, Just l ->
        let
          diemDelta = f.diem - l.diem  -- Positive = consuming
          timeDeltaMs = toTimestamp l.timestamp - toTimestamp f.timestamp
          timeDeltaHours = timeDeltaMs / (60.0 * 60.0 * 1000.0)
        in
          if timeDeltaHours > 0.0 && diemDelta > 0.0 then
            diemDelta / timeDeltaHours
          else
            0.0
      _, _ -> 0.0

-- | Calculate weighted average rate from all history
-- |
-- | **Purpose:** Calculates consumption rate using weighted average of all history,
-- |             with recency bias (more recent snapshots have higher weight).
-- | **Algorithm:**
-- | - For each consecutive pair of snapshots, calculate rate
-- | - Weight by recency: `weight = (index / total)²` (squared for stronger bias)
-- | - Return weighted average
calculateLongTermRate :: Array BalanceSnapshot -> Number
calculateLongTermRate history =
  let
    sorted = Array.sortBy (\a b -> compare (toTimestamp a.timestamp) (toTimestamp b.timestamp)) history
    total = Array.length sorted
  in
    if total < 2 then
      0.0
    else
      let
        ratesWithWeights = Array.mapWithIndex (\i snapshot ->
          if i == 0 then
            Nothing
          else
            case Array.index sorted (i - 1) of
              Just prev ->
                let
                  diemDelta = prev.diem - snapshot.diem
                  timeDeltaMs = toTimestamp snapshot.timestamp - toTimestamp prev.timestamp
                  timeDeltaHours = timeDeltaMs / (60.0 * 60.0 * 1000.0)
                in
                  if timeDeltaHours > 0.0 && diemDelta > 0.0 then
                    let
                      rate = diemDelta / timeDeltaHours
                      recency = (Number.fromInt i) / (Number.fromInt total)  -- 0 to 1
                      weight = pow recency 2.0  -- Square for stronger recency bias
                    in
                      Just { rate, weight }
                  else
                    Nothing
              Nothing -> Nothing
        ) sorted
        
        validRates = Array.catMaybes ratesWithWeights
        totalWeightedRate = Array.foldl (\acc { rate, weight } -> acc + (rate * weight)) 0.0 validRates
        totalWeight = Array.foldl (\acc { weight } -> acc + weight) 0.0 validRates
      in
        if totalWeight > 0.0 then
          totalWeightedRate / totalWeight
        else
          0.0

-- | Calculate time to depletion from current balance and consumption rate
-- |
-- | **Purpose:** Projects how long until balance reaches zero at current consumption rate.
-- | **Parameters:**
-- | - `currentDiem`: Current Diem balance
-- | - `rate`: Consumption rate in Diem per hour
-- | **Returns:** Hours until depletion (Nothing if rate <= 0 or balance <= 0)
-- | **Side Effects:** None (pure function)
-- |
-- | **Formula:** `hours = currentDiem / rate`
-- |
-- | **Example:**
-- | ```purescript
-- | timeToDepletion = calculateTimeToDepletion 10.0 2.5  -- Just 4.0 (4 hours)
-- | calculateTimeToDepletion 10.0 0.0  -- Nothing (not depleting)
-- | ```
calculateTimeToDepletion :: Number -> Number -> Maybe Number
calculateTimeToDepletion currentDiem rate
  | rate <= 0.0 = Nothing  -- Not depleting
  | currentDiem <= 0.0 = Just 0.0  -- Already depleted
  | otherwise = Just (currentDiem / rate)

-- | Calculate today's usage from balance history
-- |
-- | **Purpose:** Calculates how much Diem has been consumed today (since UTC midnight).
-- | **Parameters:**
-- | - `history`: Array of balance snapshots
-- | - `currentTime`: Current DateTime
-- | **Returns:** Diem consumed today (0.0 if cannot calculate)
-- | **Side Effects:** None (pure function)
-- |
-- | **Algorithm:**
-- | 1. Find UTC midnight (start of Diem day)
-- | 2. Filter snapshots from today
-- | 3. Calculate: first balance of day - current balance
calculateTodayUsage :: Array BalanceSnapshot -> DateTime -> Number
calculateTodayUsage history currentTime =
  let
    currentTimestamp = toTimestamp currentTime
    -- UTC midnight: set hours/minutes/seconds to 0
    -- This is simplified - in production would use proper UTC date functions
    utcMidnightTimestamp = (currentTimestamp / (24.0 * 60.0 * 60.0 * 1000.0)) # floor # (*) (24.0 * 60.0 * 60.0 * 1000.0)
    utcMidnight = fromTimestamp utcMidnightTimestamp
    
    todaySnapshots = Array.filter (\s -> toTimestamp s.timestamp >= utcMidnightTimestamp) history
    sorted = Array.sortBy (\a b -> compare (toTimestamp a.timestamp) (toTimestamp b.timestamp)) todaySnapshots
  in
    case Array.head sorted, Array.last sorted of
      Just firstOfDay, Just latest ->
        max 0.0 (firstOfDay.diem - latest.diem)
      _, _ -> 0.0
