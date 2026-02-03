-- | Auth Logout Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/auth/logout.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Auth.Logout
  ( LogoutAction(..)
  , LogoutResult(..)
  , handleLogout
  , removeCurrentAccount
  ) where

import Prelude

import Data.Array (head)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Console.App.Context.Auth (AuthSession, AccountInfo)

-- | Logout action
data LogoutAction = PerformLogout

derive instance eqLogoutAction :: Eq LogoutAction

-- | Logout result
data LogoutResult
  = LogoutSuccess { newSession :: AuthSession, redirectTo :: String }
  | LogoutNoSession { redirectTo :: String }

derive instance eqLogoutResult :: Eq LogoutResult

instance showLogoutResult :: Show LogoutResult where
  show (LogoutSuccess r) = "(LogoutSuccess " <> show r.redirectTo <> ")"
  show (LogoutNoSession r) = "(LogoutNoSession " <> show r.redirectTo <> ")"

-- | Remove current account and set new current (pure)
removeCurrentAccount :: AuthSession -> Maybe String -> AuthSession
removeCurrentAccount session currentId = case currentId of
  Nothing -> session
  Just id ->
    let
      newAccounts = Map.delete id session.account
      newCurrent = head (Map.keys newAccounts)
    in
      session { account = newAccounts, current = newCurrent }

-- | Handle logout (pure logic)
handleLogout :: AuthSession -> LogoutResult
handleLogout session = case session.current of
  Nothing -> LogoutNoSession { redirectTo: "/zen" }
  Just currentId ->
    let
      newSession = removeCurrentAccount session (Just currentId)
    in
      LogoutSuccess { newSession, redirectTo: "/zen" }

-- | Redirect URL after logout
logoutRedirectUrl :: String
logoutRedirectUrl = "/zen"
