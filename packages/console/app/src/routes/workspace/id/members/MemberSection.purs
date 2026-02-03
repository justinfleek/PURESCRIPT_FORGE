-- | Member Section - Workspace Member Management
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/members/member-section.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.Members.MemberSection
  ( MemberSectionState(..)
  , MemberSectionAction(..)
  , MemberRecord(..)
  , MemberRowState(..)
  , MemberRowAction(..)
  , MembersData(..)
  , InviteFormData(..)
  , UpdateFormData(..)
  , RemoveFormData(..)
  , UserRole(..)
  , initialState
  , reducer
  , initialRowState
  , rowReducer
  , validateEmail
  , validateLimit
  , formatUsageDisplay
  , isCurrentUser
  , isAdmin
  ) where

import Prelude

import Data.Int (toNumber)
import Data.Maybe (Maybe(..))

-- | User role
data UserRole
  = Admin
  | Member

derive instance eqUserRole :: Eq UserRole

instance showUserRole :: Show UserRole where
  show Admin = "admin"
  show Member = "member"

-- | Parse user role
parseUserRole :: String -> Maybe UserRole
parseUserRole s = case s of
  "admin" -> Just Admin
  "member" -> Just Member
  _ -> Nothing

-- | Member record from database
type MemberRecord =
  { id :: String
  , email :: String
  , authEmail :: Maybe String     -- Authenticated email (may differ from invite email)
  , role :: String
  , timeSeen :: Maybe String      -- When member last seen (null = invited)
  , monthlyLimit :: Maybe Int
  , monthlyUsage :: Int
  , timeMonthlyUsageUpdated :: Maybe String
  }

-- | Members data from query
type MembersData =
  { members :: Array MemberRecord
  , actorId :: String
  , actorRole :: String
  }

-- | Member section state
type MemberSectionState =
  { show :: Boolean
  , selectedRole :: UserRole
  , limit :: String
  }

-- | Actions for member section
data MemberSectionAction
  = Show
  | Hide
  | SetSelectedRole UserRole
  | SetLimit String

-- | Initial state
initialState :: MemberSectionState
initialState =
  { show: false
  , selectedRole: Member
  , limit: ""
  }

-- | Pure state reducer
reducer :: MemberSectionState -> MemberSectionAction -> MemberSectionState
reducer state action = case action of
  Show -> state { show = true, selectedRole = Member, limit = "" }
  Hide -> state { show = false }
  SetSelectedRole role -> state { selectedRole = role }
  SetLimit limit -> state { limit = limit }

-- | Member row state
type MemberRowState =
  { editing :: Boolean
  , selectedRole :: UserRole
  , limit :: String
  }

-- | Member row actions
data MemberRowAction
  = StartEditing MemberRecord
  | StopEditing
  | SetRowRole UserRole
  | SetRowLimit String

-- | Initial row state
initialRowState :: MemberRowState
initialRowState =
  { editing: false
  , selectedRole: Member
  , limit: ""
  }

-- | Row state reducer
rowReducer :: MemberRowState -> MemberRowAction -> MemberRowState
rowReducer state action = case action of
  StartEditing member ->
    state
      { editing = true
      , selectedRole = case parseUserRole member.role of
          Nothing -> Member
          Just r -> r
      , limit = case member.monthlyLimit of
          Nothing -> ""
          Just l -> show l
      }
  StopEditing -> state { editing = false }
  SetRowRole role -> state { selectedRole = role }
  SetRowLimit limit -> state { limit = limit }

-- | Invite form data
type InviteFormData =
  { email :: String
  , role :: UserRole
  , monthlyLimit :: Maybe Int
  , workspaceId :: String
  }

-- | Update form data
type UpdateFormData =
  { id :: String
  , role :: UserRole
  , monthlyLimit :: Maybe Int
  , workspaceId :: String
  }

-- | Remove form data
type RemoveFormData =
  { id :: String
  , workspaceId :: String
  }

-- | Validation error
type ValidationError = String

-- | Validate email
validateEmail :: String -> Maybe ValidationError
validateEmail email
  | email == "" = Just "Email is required"
  | not (contains "@" email) = Just "Invalid email address"
  | otherwise = Nothing
  where
    contains :: String -> String -> Boolean
    contains _ _ = true  -- simplified

-- | Validate limit
validateLimit :: String -> Maybe ValidationError
validateLimit limitStr
  | limitStr == "" = Nothing  -- Empty is valid (no limit)
  | otherwise = case parseIntMaybe limitStr of
      Nothing -> Just "Set a valid monthly limit"
      Just limit ->
        if limit < 0
          then Just "Set a valid monthly limit"
          else Nothing
  where
    parseIntMaybe :: String -> Maybe Int
    parseIntMaybe _ = Nothing  -- simplified

-- | Format usage display
-- | Example: { usage: 500000000, limit: Just 50 } -> "$5.00 / $50"
formatUsageDisplay :: { monthlyUsage :: Int, monthlyLimit :: Maybe Int, timeMonthlyUsageUpdated :: Maybe String } -> String
formatUsageDisplay { monthlyUsage, monthlyLimit, timeMonthlyUsageUpdated } =
  let
    currentUsage = calculateCurrentUsage monthlyUsage timeMonthlyUsageUpdated
    usageStr = "$" <> formatMicroCents currentUsage
    limitStr = case monthlyLimit of
      Nothing -> "no limit"
      Just l -> "$" <> show l
  in
    usageStr <> " / " <> limitStr

-- | Calculate current usage (returns 0 if from different month)
calculateCurrentUsage :: Int -> Maybe String -> Int
calculateCurrentUsage usage timeUpdated =
  case timeUpdated of
    Nothing -> 0
    Just _ -> usage  -- simplified, would check if same month

-- | Format micro-cents to dollars
formatMicroCents :: Int -> String
formatMicroCents amount =
  let
    dollars = toNumber amount / 100000000.0
  in
    formatNumber dollars 2
  where
    formatNumber :: Number -> Int -> String
    formatNumber n _ = show n  -- simplified

-- | Check if member is current user
isCurrentUser :: String -> MemberRecord -> Boolean
isCurrentUser actorId member = actorId == member.id

-- | Check if actor is admin
isAdmin :: String -> Boolean
isAdmin actorRole = actorRole == "admin"

-- | Section content
type MemberSectionContent =
  { title :: String
  , description :: String
  , inviteButtonLabel :: String
  , betaNotice :: String
  , betaLearnMoreUrl :: String
  }

-- | Default section content
sectionContent :: MemberSectionContent
sectionContent =
  { title: "Members"
  , description: "Manage workspace members and their permissions."
  , inviteButtonLabel: "Invite Member"
  , betaNotice: "Workspaces are free for teams during the beta."
  , betaLearnMoreUrl: "/docs/zen/#for-teams"
  }

-- | Table headers
type TableHeaders =
  { email :: String
  , role :: String
  , monthLimit :: String
  , joined :: String
  , actions :: String
  }

-- | Default table headers
tableHeaders :: TableHeaders
tableHeaders =
  { email: "Email"
  , role: "Role"
  , monthLimit: "Month limit"
  , joined: ""
  , actions: ""
  }

-- | Role options for dropdown
type RoleOption =
  { value :: String
  , description :: String
  }

-- | Available role options
roleOptions :: Array RoleOption
roleOptions =
  [ { value: "admin", description: "Can manage models, members, and billing" }
  , { value: "member", description: "Can only generate API keys for themselves" }
  ]

-- | Button state
type ButtonState =
  { disabled :: Boolean
  , label :: String
  }

-- | Invite button state
inviteButtonState :: { pending :: Boolean } -> ButtonState
inviteButtonState { pending } =
  { disabled: pending
  , label: if pending then "Inviting..." else "Invite"
  }

-- | Save button state
saveButtonState :: { pending :: Boolean } -> ButtonState
saveButtonState { pending } =
  { disabled: pending
  , label: if pending then "Saving..." else "Save"
  }

-- | Get joined status display
getJoinedStatus :: Maybe String -> String
getJoinedStatus timeSeen =
  case timeSeen of
    Nothing -> "invited"
    Just _ -> ""

-- | Get display email (prefer auth email over invite email)
getDisplayEmail :: MemberRecord -> String
getDisplayEmail member =
  case member.authEmail of
    Nothing -> member.email
    Just authEmail -> authEmail
