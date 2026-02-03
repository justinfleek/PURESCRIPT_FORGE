-- | Console.Core.Database - Database Access Layer
-- |
-- | **What:** Provides type-safe database operations using connection pooling
-- |         and transaction management. All queries are parameterized to prevent
-- |         SQL injection.
-- | **Why:** Database access must be safe (no injection), efficient (pooling),
-- |         and transactional (ACID guarantees). Type safety ensures queries
-- |         return expected types.
-- | **How:** Uses connection pool with configurable size. Transactions use
-- |         MySQL InnoDB with automatic rollback on exception.
-- |
-- | **Dependencies:**
-- | - Effect.Aff: Async operations
-- | - Console.Core.Types: Domain types
-- |
-- | **Mathematical Foundation:**
-- | - **Transaction Isolation:** REPEATABLE READ (InnoDB default)
-- | - **Atomicity:** All operations in transaction succeed or all fail
-- | - **Connection Pool:** Bounded resource (max N connections)
-- |
-- | **Security Properties:**
-- | - All queries use parameterized statements (no string interpolation)
-- | - Connections returned to pool on completion/error
-- | - Sensitive data not logged
-- |
-- | **Corresponding Haskell:** `console-hs/src/Console/Database.hs`
module Console.Core.Database
  ( -- * Database Operations
    Database
  , use
  , transaction
    -- * Query Types
  , Query
  , SelectQuery
  , InsertQuery
  , UpdateQuery
  , DeleteQuery
    -- * Query Builders
  , select
  , insert
  , update
  , delete
  , where_
  , and_
  , or_
  , eq
  , isNull
  , isNotNull
  , orderBy
  , limit
  , offset
  ) where

import Prelude

import Control.Monad.Reader (ReaderT)
import Data.Array ((:))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff, liftAff)

-- ═══════════════════════════════════════════════════════════════════════════════
-- DATABASE MONAD
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Database context type (opaque)
foreign import data DatabaseContext :: Type

-- | Database monad
type Database a = ReaderT DatabaseContext Aff a

-- | Run database operation with connection from pool
use :: forall a. Database a -> Aff a
use = runDatabaseFFI

-- | Run database operation in transaction
-- | Automatically commits on success, rollbacks on exception
transaction :: forall a. Database a -> Aff a
transaction = runTransactionFFI

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERY TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base query type
data Query a
  = SelectQ (SelectQuery a)
  | InsertQ InsertQuery
  | UpdateQ UpdateQuery
  | DeleteQ DeleteQuery

-- | SELECT query builder
type SelectQuery a =
  { table :: String
  , columns :: Array String
  , conditions :: Array Condition
  , orderBy :: Maybe { column :: String, direction :: OrderDirection }
  , limit :: Maybe Int
  , offset :: Maybe Int
  }

-- | INSERT query builder
type InsertQuery =
  { table :: String
  , columns :: Array String
  , values :: Array QueryValue
  , onDuplicateUpdate :: Maybe (Array { column :: String, value :: QueryValue })
  }

-- | UPDATE query builder
type UpdateQuery =
  { table :: String
  , sets :: Array { column :: String, value :: QueryValue }
  , conditions :: Array Condition
  }

-- | DELETE query builder
type DeleteQuery =
  { table :: String
  , conditions :: Array Condition
  }

-- | Query condition
data Condition
  = Eq String QueryValue
  | IsNull String
  | IsNotNull String
  | And Condition Condition
  | Or Condition Condition

-- | Query value (parameterized)
data QueryValue
  = StringVal String
  | IntVal Int
  | BoolVal Boolean
  | NullVal
  | SqlNow  -- SQL NOW() function

-- | Order direction
data OrderDirection = Asc | Desc

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERY BUILDERS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create SELECT query
select :: forall a. String -> Array String -> SelectQuery a
select table columns =
  { table
  , columns
  , conditions: []
  , orderBy: Nothing
  , limit: Nothing
  , offset: Nothing
  }

-- | Create INSERT query
insert :: String -> Array { column :: String, value :: QueryValue } -> InsertQuery
insert table values =
  { table
  , columns: map _.column values
  , values: map _.value values
  , onDuplicateUpdate: Nothing
  }

-- | Create UPDATE query
update :: String -> Array { column :: String, value :: QueryValue } -> UpdateQuery
update table sets =
  { table
  , sets
  , conditions: []
  }

-- | Create DELETE query
delete :: String -> DeleteQuery
delete table =
  { table
  , conditions: []
  }

-- | Add WHERE condition to SELECT
where_ :: forall a. Condition -> SelectQuery a -> SelectQuery a
where_ cond q = q { conditions = cond : q.conditions }

-- | Combine conditions with AND
and_ :: Condition -> Condition -> Condition
and_ = And

-- | Combine conditions with OR
or_ :: Condition -> Condition -> Condition
or_ = Or

-- | Equality condition
eq :: String -> QueryValue -> Condition
eq = Eq

-- | IS NULL condition
isNull :: String -> Condition
isNull = IsNull

-- | IS NOT NULL condition
isNotNull :: String -> Condition
isNotNull = IsNotNull

-- | Add ORDER BY to SELECT
orderBy :: forall a. String -> OrderDirection -> SelectQuery a -> SelectQuery a
orderBy column direction q = q { orderBy = Just { column, direction } }

-- | Add LIMIT to SELECT
limit :: forall a. Int -> SelectQuery a -> SelectQuery a
limit n q = q { limit = Just n }

-- | Add OFFSET to SELECT
offset :: forall a. Int -> SelectQuery a -> SelectQuery a
offset n q = q { offset = Just n }

-- ═══════════════════════════════════════════════════════════════════════════════
-- FFI
-- ═══════════════════════════════════════════════════════════════════════════════

foreign import runDatabaseFFI :: forall a. Database a -> Aff a
foreign import runTransactionFFI :: forall a. Database a -> Aff a
