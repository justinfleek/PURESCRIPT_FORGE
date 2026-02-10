-- | Database Sync - Periodic synchronization between SQLite and DuckDB
module Bridge.Database.Sync where

import Prelude
import Effect.Aff (Aff, delay)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Int (toNumber)
import Data.Time.Duration (Milliseconds(..))
import Bridge.FFI.Haskell.Database as DB
import Bridge.FFI.Haskell.Analytics as DuckDB
import Bridge.FFI.Node.Pino as Pino

-- | FFI declarations (top-level)
foreign import getCurrentTimeMillis :: Aff Number
foreign import trySyncImpl :: DB.Database -> DuckDB.AnalyticsDB -> EffectFnAff (Either String Unit)

-- | Sync SQLite data to DuckDB for analytics
syncData :: DB.Database -> DuckDB.AnalyticsDB -> Aff (Either String Unit)
syncData db analyticsDb = fromEffectFnAff $ trySyncImpl db analyticsDb

-- | Start periodic sync loop
startPeriodicSync :: DB.Database -> DuckDB.AnalyticsDB -> Int -> Pino.Logger -> Aff Unit
startPeriodicSync db analyticsDb intervalMinutes logger = go
  where
    intervalMs = Milliseconds (toNumber (intervalMinutes * 60 * 1000))

    go :: Aff Unit
    go = do
      delay intervalMs
      result <- syncData db analyticsDb
      case result of
        Right _ -> liftEffect $ Pino.info logger "Database sync completed"
        Left err -> liftEffect $ Pino.error logger ("Database sync failed: " <> err)
      go
