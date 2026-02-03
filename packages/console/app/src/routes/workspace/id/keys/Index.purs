-- | Keys Index Page
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/keys/index.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.Keys.Index
  ( KeysPageContent(..)
  ) where

import Prelude

-- | Keys page content structure
type KeysPageContent =
  { page :: String
  , slot :: String
  }

-- | Default page content
keysPageContent :: KeysPageContent
keysPageContent =
  { page: "workspace-[id]"
  , slot: "sections"
  }
