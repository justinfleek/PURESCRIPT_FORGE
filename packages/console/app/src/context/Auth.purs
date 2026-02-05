-- | Authentication Context
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/context/auth.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Context.Auth
  ( AuthSession
  , AuthClient
  , AccountInfo
  , SessionConfig
  , CookieConfig
  , ActorResult(..)
  , emptySession
  , mkAuthClient
  , mkSessionConfig
  , defaultSessionConfig
  , getActorFromSession
  , updateCurrentAccount
  , buildUserQuery
  , updateUserSeen
  ) where

import Prelude

import Data.Array (head, index, fromFoldable)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Either (Either(..))
import Data.Tuple (Tuple(..))
import Forge.Console.Core.Actor (ActorInfo(..), ActorType(..), AccountActor, UserActor, UserRole(..))
import Forge.Console.Core.Identifier (AccountId, UserId, WorkspaceId)

-- | Parse role string to UserRole
parseRole :: String -> UserRole
parseRole "admin" = Admin
parseRole _ = Member

-- | Account information stored in session
type AccountInfo =
  { id :: String
  , email :: String
  }

-- | Auth session data structure
type AuthSession =
  { account :: Map String AccountInfo
  , current :: Maybe String
  }

-- | Empty auth session
emptySession :: AuthSession
emptySession =
  { account: Map.empty
  , current: Nothing
  }

-- | Cookie configuration
type CookieConfig =
  { secure :: Boolean
  , httpOnly :: Boolean
  }

-- | Session configuration
type SessionConfig =
  { password :: String
  , name :: String
  , maxAge :: Int  -- seconds
  , cookie :: CookieConfig
  }

-- | Default session config (1 year expiry)
defaultSessionConfig :: String -> SessionConfig
defaultSessionConfig password =
  { password: password
  , name: "auth"
  , maxAge: 60 * 60 * 24 * 365  -- 1 year in seconds
  , cookie:
      { secure: false
      , httpOnly: true
      }
  }

-- | Smart constructor for session config
mkSessionConfig :: String -> String -> Int -> CookieConfig -> Either String SessionConfig
mkSessionConfig password name maxAge cookie
  | password == "" = Left "Session password is required"
  | name == "" = Left "Session name is required"
  | maxAge <= 0 = Left "Max age must be positive"
  | otherwise = Right { password, name, maxAge, cookie }

-- | Auth client configuration
type AuthClient =
  { clientID :: String
  , issuer :: String
  }

-- | Smart constructor for auth client
mkAuthClient :: String -> String -> Either String AuthClient
mkAuthClient clientID issuer
  | clientID == "" = Left "Client ID is required"
  | issuer == "" = Left "Issuer URL is required"
  | otherwise = Right { clientID, issuer }

-- | Default auth client (app)
defaultAuthClient :: String -> AuthClient
defaultAuthClient issuer =
  { clientID: "app"
  , issuer: issuer
  }

-- | Result of getting actor from session
data ActorResult
  = ActorAccount AccountActor
  | ActorUser UserActor
  | ActorPublic
  | ActorRedirect String

derive instance eqActorResult :: Eq ActorResult

instance showActorResult :: Show ActorResult where
  show (ActorAccount p) = "(ActorAccount " <> show p <> ")"
  show (ActorUser p) = "(ActorUser " <> show p <> ")"
  show ActorPublic = "ActorPublic"
  show (ActorRedirect url) = "(ActorRedirect " <> show url <> ")"

-- | Get actor info from session (pure logic)
-- | Returns the appropriate actor type based on session state and workspace
getActorFromSession 
  :: AuthSession 
  -> Maybe String  -- workspace ID
  -> Maybe { userId :: String, workspaceId :: String, accountId :: String, role :: String }  -- user lookup result
  -> ActorResult
getActorFromSession session workspaceM userLookup = case workspaceM of
  -- No workspace specified - return account or public actor
  Nothing ->
    case session.current of
      Just currentId ->
        case Map.lookup currentId session.account of
          Just info -> ActorAccount { email: info.email, accountID: info.id }
          Nothing ->
            -- Current not found, try first account
            case head (fromFoldable (Map.values session.account)) of
              Just info -> ActorAccount { email: info.email, accountID: info.id }
              Nothing -> ActorPublic
      Nothing ->
        -- No current, try first account
        case head (fromFoldable (Map.values session.account)) of
          Just info -> ActorAccount { email: info.email, accountID: info.id }
          Nothing -> ActorPublic
  
  -- Workspace specified - need user lookup
  Just workspace ->
    if Map.isEmpty session.account then
      ActorRedirect "/auth/authorize"
    else
      case userLookup of
        Just user -> ActorUser
          { userID: user.userId
          , workspaceID: user.workspaceId
          , accountID: user.accountId
          , role: parseRole user.role
          }
        Nothing -> ActorRedirect "/auth/authorize"

-- | Update current account in session (pure)
updateCurrentAccount :: AuthSession -> String -> AuthSession
updateCurrentAccount session newCurrentId =
  session { current = Just newCurrentId }

-- | Add account to session (pure)
addAccountToSession :: AuthSession -> String -> AccountInfo -> AuthSession
addAccountToSession session accountId info =
  session { account = Map.insert accountId info session.account }

-- | Remove account from session (pure)
removeAccountFromSession :: AuthSession -> String -> AuthSession
removeAccountFromSession session accountId =
  session { account = Map.delete accountId session.account }

-- | Build user lookup query parameters (pure)
-- | Returns workspace ID and array of account IDs for database query
buildUserQuery :: AuthSession -> String -> Maybe { workspaceId :: String, accountIds :: Array String }
buildUserQuery session workspaceId =
  let accountIds = fromFoldable (Map.keys session.account)
  in if accountIds == [] 
     then Nothing
     else Just { workspaceId, accountIds }

-- | Check if session has any accounts
hasAccounts :: AuthSession -> Boolean
hasAccounts session = not (Map.isEmpty session.account)

-- | Get all account IDs from session
getAccountIds :: AuthSession -> Array String
getAccountIds session = fromFoldable (Map.keys session.account)

-- | SQL template for user seen update (pure data)
type UpdateUserSeenQuery =
  { table :: String
  , setColumn :: String
  , whereWorkspace :: String
  , whereUserId :: String
  }

-- | Build update user seen query structure (pure)
updateUserSeen :: String -> String -> UpdateUserSeenQuery
updateUserSeen workspaceId userId =
  { table: "UserTable"
  , setColumn: "timeSeen"
  , whereWorkspace: workspaceId
  , whereUserId: userId
  }
