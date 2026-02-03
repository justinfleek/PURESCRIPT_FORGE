-- | Workspace Layout Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.WorkspaceLayout
  ( WorkspaceLayoutProps(..)
  ) where

import Prelude

import Data.Maybe (Maybe)

-- | Workspace layout props
type WorkspaceLayoutProps =
  { workspaceId :: String
  , userEmail :: Maybe String
  }
