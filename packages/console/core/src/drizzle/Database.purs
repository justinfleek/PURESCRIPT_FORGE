-- | Database Module
-- |
-- | Provides database operations using pure functional patterns.
-- | Uses Free monad for database DSL that can be interpreted.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/drizzle/index.ts
module Forge.Console.Core.Drizzle.Database
  ( DatabaseF(..)
  , Database
  , Query(..)
  , InsertQuery
  , SelectQuery
  , UpdateQuery
  , DeleteQuery
  , insert
  , select
  , update
  , delete
  , transaction
  , runQuery
  ) where

import Prelude

import Control.Monad.Free (Free, liftF)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- | Insert query parameters
type InsertQuery =
  { table :: String
  , values :: Foreign  -- Type-erased values using Foreign
  }

-- | Select query parameters
type SelectQuery =
  { table :: String
  , where_ :: Maybe String
  }

-- | Update query parameters
type UpdateQuery =
  { table :: String
  , set :: Foreign  -- Type-erased set values using Foreign
  , where_ :: Maybe String
  }

-- | Delete query parameters
type DeleteQuery =
  { table :: String
  , where_ :: Maybe String
  }

-- | Query types
data Query
  = InsertQ InsertQuery
  | SelectQ SelectQuery
  | UpdateQ UpdateQuery
  | DeleteQ DeleteQuery

-- Note: Cannot derive Eq due to Foreign not having Eq instance

-- | Database operations as a functor
data DatabaseF next
  = RunInsert InsertQuery next
  | RunSelect SelectQuery next
  | RunUpdate UpdateQuery next
  | RunDelete DeleteQuery next
  | RunTransaction (Database Unit) (Unit -> next)

derive instance functorDatabaseF :: Functor DatabaseF

-- | Free monad for database operations
type Database a = Free DatabaseF a

-- | Insert a record
-- | The values parameter is type-erased via Foreign for the DSL
insert :: InsertQuery -> Database Unit
insert query = liftF $ RunInsert query unit

-- | Select records
select :: SelectQuery -> Database Unit
select query = liftF $ RunSelect query unit

-- | Update records
update :: UpdateQuery -> Database Unit
update query = liftF $ RunUpdate query unit

-- | Delete records
delete :: DeleteQuery -> Database Unit
delete query = liftF $ RunDelete query unit

-- | Run operations in a transaction
transaction :: Database Unit -> Database Unit
transaction db = liftF $ RunTransaction db identity

-- | Run a query (placeholder - actual implementation would interpret)
runQuery :: Query -> Either String Unit
runQuery _ = Left "Database interpreter not implemented - this is a pure DSL"
