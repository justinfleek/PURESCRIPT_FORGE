-- | Haskell Database FFI - SQLite operations via Haskell child process
module Bridge.FFI.Haskell.Database where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Data.Either (Either)
import Data.Maybe (Maybe)

-- | Opaque Database handle
foreign import data Database :: Type

-- | Open database connection
foreign import openDatabaseImpl :: String -> EffectFnAff Database

-- | Close database connection
foreign import closeDatabaseImpl :: Database -> EffectFnAff Unit

-- | Save snapshot
foreign import saveSnapshotImpl :: Database -> String -> String -> Maybe String -> Maybe String -> EffectFnAff (Either String String)

-- | Get snapshot by ID
foreign import getSnapshotImpl :: Database -> String -> EffectFnAff (Either String String)

-- | List snapshots
foreign import listSnapshotsImpl :: Database -> Maybe Int -> Maybe Int -> EffectFnAff (Either String String)

-- | Delete snapshot
foreign import deleteSnapshotImpl :: Database -> String -> EffectFnAff (Either String Boolean)

-- | Save session record
foreign import saveSessionImpl :: Database -> String -> EffectFnAff (Either String String)

-- | Get sessions by session ID
foreign import getSessionsBySessionIdImpl :: Database -> String -> EffectFnAff (Either String String)

-- | Record balance history
foreign import recordBalanceHistoryImpl :: Database -> Number -> Number -> Number -> Number -> Maybe Int -> EffectFnAff (Either String String)

-- | Save settings
foreign import saveSettingsImpl :: Database -> String -> String -> EffectFnAff (Either String Unit)

-- | Get settings
foreign import getSettingsImpl :: Database -> String -> EffectFnAff (Either String (Maybe String))

-- | Get balance history
foreign import getBalanceHistoryImpl :: Database -> Maybe Int -> Maybe Int -> EffectFnAff (Either String String)

-- | Open database
openDatabase :: String -> Aff Database
openDatabase path = fromEffectFnAff $ openDatabaseImpl path

-- | Close database
closeDatabase :: Database -> Aff Unit
closeDatabase db = fromEffectFnAff $ closeDatabaseImpl db

-- | Save snapshot
saveSnapshot :: Database -> String -> String -> Maybe String -> Maybe String -> Aff (Either String String)
saveSnapshot db stateHash jsonData trigger description =
  fromEffectFnAff $ saveSnapshotImpl db stateHash jsonData trigger description

-- | Get snapshot
getSnapshot :: Database -> String -> Aff (Either String String)
getSnapshot db snapshotId = fromEffectFnAff $ getSnapshotImpl db snapshotId

-- | List snapshots
listSnapshots :: Database -> Maybe Int -> Maybe Int -> Aff (Either String String)
listSnapshots db limit offset = fromEffectFnAff $ listSnapshotsImpl db limit offset

-- | Delete snapshot
deleteSnapshot :: Database -> String -> Aff (Either String Boolean)
deleteSnapshot db snapshotId = fromEffectFnAff $ deleteSnapshotImpl db snapshotId

-- | Save session
saveSession :: Database -> String -> Aff (Either String String)
saveSession db sessionJson = fromEffectFnAff $ saveSessionImpl db sessionJson

-- | Get sessions by session ID
getSessionsBySessionId :: Database -> String -> Aff (Either String String)
getSessionsBySessionId db sessionId = fromEffectFnAff $ getSessionsBySessionIdImpl db sessionId

-- | Record balance history
recordBalanceHistory :: Database -> Number -> Number -> Number -> Number -> Maybe Int -> Aff (Either String String)
recordBalanceHistory db diem usd effective rate ttd =
  fromEffectFnAff $ recordBalanceHistoryImpl db diem usd effective rate ttd

-- | Save settings
saveSettings :: Database -> String -> String -> Aff (Either String Unit)
saveSettings db key value = fromEffectFnAff $ saveSettingsImpl db key value

-- | Get settings
getSettings :: Database -> String -> Aff (Either String (Maybe String))
getSettings db key = fromEffectFnAff $ getSettingsImpl db key

-- | Get balance history
getBalanceHistory :: Database -> Maybe Int -> Maybe Int -> Aff (Either String String)
getBalanceHistory db limit offset = fromEffectFnAff $ getBalanceHistoryImpl db limit offset
