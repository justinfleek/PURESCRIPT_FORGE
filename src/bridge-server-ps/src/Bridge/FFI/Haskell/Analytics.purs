-- | DuckDB Analytics FFI Bindings
-- | PureScript interface to Haskell DuckDB analytics
module Bridge.FFI.Haskell.Analytics where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Maybe (Maybe)

-- | Opaque Analytics Handle type
foreign import data AnalyticsHandle :: Type

-- | Open analytics database
foreign import openAnalytics :: Maybe String -> Effect AnalyticsHandle

-- | Close analytics database
foreign import closeAnalytics :: AnalyticsHandle -> Effect Unit

-- | Load data from SQLite into DuckDB
foreign import loadFromSQLite :: AnalyticsHandle -> String -> Aff Unit

-- | Query token usage by model
foreign import queryTokenUsageByModel :: AnalyticsHandle -> String -> String -> Aff String -- Returns JSON

-- | Query cost trends
foreign import queryCostTrends :: AnalyticsHandle -> String -> String -> Aff String -- Returns JSON

-- | Query top sessions by cost
foreign import queryTopSessionsByCost :: AnalyticsHandle -> Int -> Aff String -- Returns JSON

-- | Query model performance
foreign import queryModelPerformance :: AnalyticsHandle -> Aff String -- Returns JSON

-- | Query balance consumption
foreign import queryBalanceConsumption :: AnalyticsHandle -> String -> String -> Aff String -- Returns JSON

-- | Query daily summary
foreign import queryDailySummary :: AnalyticsHandle -> String -> String -> Aff String -- Returns JSON
