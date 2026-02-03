-- | Members Index Page
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/members/index.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.Members.Index
  ( MembersPageContent(..)
  ) where

import Prelude

-- | Members page content structure
type MembersPageContent =
  { page :: String
  , slot :: String
  }

-- | Default page content
membersPageContent :: MembersPageContent
membersPageContent =
  { page: "workspace-[id]"
  , slot: "sections"
  }
