-- | Auth Index Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/auth/index.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Auth.Index
  ( AuthIndexResult(..)
  , handleAuthIndex
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))

-- | Auth index route result
data AuthIndexResult
  = RedirectToWorkspace String
  | RedirectToAuthorize

derive instance eqAuthIndexResult :: Eq AuthIndexResult

instance showAuthIndexResult :: Show AuthIndexResult where
  show (RedirectToWorkspace id) = "(RedirectToWorkspace " <> show id <> ")"
  show RedirectToAuthorize = "RedirectToAuthorize"

-- | Handle auth index route (pure)
-- | Redirects to last seen workspace or to authorize
handleAuthIndex :: Maybe String -> AuthIndexResult
handleAuthIndex lastSeenWorkspaceId = case lastSeenWorkspaceId of
  Just workspaceId -> RedirectToWorkspace ("/workspace/" <> workspaceId)
  Nothing -> RedirectToAuthorize

-- | Build redirect URL for workspace
workspaceRedirectUrl :: String -> String
workspaceRedirectUrl workspaceId = "/workspace/" <> workspaceId

-- | Authorize redirect URL
authorizeRedirectUrl :: String
authorizeRedirectUrl = "/auth/authorize"
