-- | Settings Index Page
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/settings/index.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.Settings.Index
  ( SettingsPageContent(..)
  ) where

import Prelude

-- | Settings page content structure
type SettingsPageContent =
  { page :: String
  , slot :: String
  }

-- | Default page content
settingsPageContent :: SettingsPageContent
settingsPageContent =
  { page: "workspace-[id]"
  , slot: "sections"
  }
