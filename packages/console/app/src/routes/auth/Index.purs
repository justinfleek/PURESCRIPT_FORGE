-- | Auth Index Route Handler
-- |
-- | Redirects to last seen workspace or auth authorize page.
-- | PureScript wrapper around SolidJS Start route handler.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/auth/index.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Auth.Index
  ( handleAuthIndex
  , AuthIndexResult(..)
  ) where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Maybe (Maybe(..))
import Console.App.FFI.SolidStart (APIEvent, redirect)
import Console.App.Routes.Workspace.Common (getLastSeenWorkspaceID)

-- | Auth index result
data AuthIndexResult
  = RedirectToWorkspace String
  | RedirectToAuthorize

derive instance eqAuthIndexResult :: Eq AuthIndexResult

instance showAuthIndexResult :: Show AuthIndexResult where
  show (RedirectToWorkspace id) = "RedirectToWorkspace(" <> id <> ")"
  show RedirectToAuthorize = "RedirectToAuthorize"

-- | Handle auth index route
-- | Tries to get last seen workspace, redirects to authorize if none found
handleAuthIndex :: APIEvent -> Aff AuthIndexResult
handleAuthIndex _event = do
  workspaceId <- liftEffect getLastSeenWorkspaceID
  case workspaceId of
    Just id -> pure (RedirectToWorkspace id)
    Nothing -> pure RedirectToAuthorize

-- | Get redirect URL from result
getRedirectUrl :: AuthIndexResult -> String
getRedirectUrl (RedirectToWorkspace id) = "/workspace/" <> id
getRedirectUrl RedirectToAuthorize = "/auth/authorize"
