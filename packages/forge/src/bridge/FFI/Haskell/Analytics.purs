-- | DuckDB Analytics FFI - High-performance analytical queries via Haskell
module Bridge.FFI.Haskell.Analytics where

import Prelude
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Data.Either (Either)
import Data.Maybe (Maybe)

-- | Opaque Analytics DB handle
foreign import data AnalyticsDB :: Type

-- | FFI implementations
foreign import openAnalyticsImpl :: Maybe String -> EffectFnAff AnalyticsDB
foreign import closeAnalyticsImpl :: AnalyticsDB -> EffectFnAff Unit
foreign import loadFromSQLiteImpl :: AnalyticsDB -> String -> EffectFnAff (Either String Unit)
foreign import queryTokenUsageByModelImpl :: AnalyticsDB -> String -> String -> EffectFnAff (Either String String)
foreign import queryCostTrendsImpl :: AnalyticsDB -> String -> String -> EffectFnAff (Either String String)
foreign import queryTopSessionsByCostImpl :: AnalyticsDB -> Int -> EffectFnAff (Either String String)
foreign import queryModelPerformanceImpl :: AnalyticsDB -> EffectFnAff (Either String String)
foreign import queryBalanceConsumptionImpl :: AnalyticsDB -> String -> String -> EffectFnAff (Either String String)
foreign import queryDailySummaryImpl :: AnalyticsDB -> String -> String -> EffectFnAff (Either String String)

-- | Open analytics database (optional file path, defaults to in-memory)
openAnalytics :: Maybe String -> Aff AnalyticsDB
openAnalytics path = fromEffectFnAff $ openAnalyticsImpl path

-- | Close analytics database
closeAnalytics :: AnalyticsDB -> Aff Unit
closeAnalytics db = fromEffectFnAff $ closeAnalyticsImpl db

-- | Load data from SQLite into DuckDB for analysis
loadFromSQLite :: AnalyticsDB -> String -> Aff (Either String Unit)
loadFromSQLite db sqlitePath = fromEffectFnAff $ loadFromSQLiteImpl db sqlitePath

-- | Query token usage grouped by model (returns JSON)
queryTokenUsageByModel :: AnalyticsDB -> String -> String -> Aff (Either String String)
queryTokenUsageByModel db startTime endTime =
  fromEffectFnAff $ queryTokenUsageByModelImpl db startTime endTime

-- | Query cost trends over time (returns JSON)
queryCostTrends :: AnalyticsDB -> String -> String -> Aff (Either String String)
queryCostTrends db startTime endTime =
  fromEffectFnAff $ queryCostTrendsImpl db startTime endTime

-- | Query top N sessions by cost (returns JSON)
queryTopSessionsByCost :: AnalyticsDB -> Int -> Aff (Either String String)
queryTopSessionsByCost db limit =
  fromEffectFnAff $ queryTopSessionsByCostImpl db limit

-- | Query model performance metrics (returns JSON)
queryModelPerformance :: AnalyticsDB -> Aff (Either String String)
queryModelPerformance db = fromEffectFnAff $ queryModelPerformanceImpl db

-- | Query balance consumption over time (returns JSON)
queryBalanceConsumption :: AnalyticsDB -> String -> String -> Aff (Either String String)
queryBalanceConsumption db startTime endTime =
  fromEffectFnAff $ queryBalanceConsumptionImpl db startTime endTime

-- | Query daily summary (returns JSON)
queryDailySummary :: AnalyticsDB -> String -> String -> Aff (Either String String)
queryDailySummary db startTime endTime =
  fromEffectFnAff $ queryDailySummaryImpl db startTime endTime
