-- | Haskell Database FFI Bindings
-- | PureScript interface to Haskell database operations
module Bridge.FFI.Haskell.Database where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Maybe (Maybe)

-- | Opaque Database Handle type
foreign import data DatabaseHandle :: Type

-- | Open database
foreign import openDatabase :: String -> Effect DatabaseHandle

-- | Close database
foreign import closeDatabase :: DatabaseHandle -> Effect Unit

-- | Save snapshot
foreign import saveSnapshot :: DatabaseHandle -> String -> String -> String -> String -> Maybe String -> Maybe String -> Aff String

-- | Get snapshot
foreign import getSnapshot :: DatabaseHandle -> String -> Aff (Maybe String) -- Returns JSON

-- | List snapshots
foreign import listSnapshots :: DatabaseHandle -> Maybe Int -> Maybe Int -> Aff String -- Returns JSON array

-- | Delete snapshot
foreign import deleteSnapshot :: DatabaseHandle -> String -> Aff Boolean

-- | Save session
foreign import saveSession :: DatabaseHandle -> String -> String -> Int -> Int -> Int -> Number -> String -> String -> String -> Maybe String -> Aff String

-- | Get sessions by session ID
foreign import getSessionsBySessionId :: DatabaseHandle -> String -> Aff String -- Returns JSON array

-- | Record balance history
foreign import recordBalanceHistory :: DatabaseHandle -> Number -> Number -> Number -> Number -> Maybe Int -> Aff String

-- | Get balance history
foreign import getBalanceHistory :: DatabaseHandle -> Maybe Int -> Maybe Int -> Aff String -- Returns JSON array

-- | Save settings
foreign import saveSettings :: DatabaseHandle -> String -> String -> Aff Unit

-- | Get settings
foreign import getSettings :: DatabaseHandle -> String -> Aff (Maybe String)
