-- | Debug Index Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/debug/index.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Debug.Index
  ( DebugResponse(..)
  , handleGet
  ) where

import Prelude

-- | Debug response data
type DebugResponse =
  { data :: Int  -- User count
  }

-- | Handle GET request (pure structure)
-- | Returns user count from database
handleGet :: Int -> DebugResponse
handleGet userCount = { data: userCount }

-- | Query configuration (pure data)
type DebugQuery =
  { table :: String
  , operation :: String
  }

userCountQuery :: DebugQuery
userCountQuery =
  { table: "UserTable"
  , operation: "count"
  }
