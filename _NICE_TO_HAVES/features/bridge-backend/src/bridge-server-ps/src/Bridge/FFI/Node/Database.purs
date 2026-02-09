-- | better-sqlite3 FFI bindings
module Bridge.FFI.Node.Database where

import Prelude
import Effect (Effect)
import Data.Either (Either)

-- | Opaque Database type
foreign import data Database :: Type

-- | Opaque Statement type
foreign import data Statement :: Type

-- | Open database
foreign import open :: String -> Effect Database

-- | Close database
foreign import close :: Database -> Effect Unit

-- | Execute SQL (no return)
foreign import exec :: Database -> String -> Effect Unit

-- | Prepare statement
foreign import prepare :: Database -> String -> Effect Statement

-- | Run statement (no return)
foreign import run :: Statement -> Array String -> Effect Unit

-- | Get one row
foreign import get :: Statement -> Array String -> Effect (Either String String)

-- | Get all rows
foreign import all :: Statement -> Array String -> Effect (Either String String)

-- | Generate UUID
-- | For deterministic operations, use generateUUIDFromSeed
foreign import randomUUID :: Effect String

-- | Generate deterministic UUID from namespace and seed
-- | Same namespace + seed always produces same UUID
foreign import generateUUIDFromSeed :: String -> Int -> String
