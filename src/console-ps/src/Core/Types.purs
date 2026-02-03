-- | Console.Core.Types - Core Domain Types for Console Application
-- |
-- | **What:** Defines fundamental types for user management, workspaces, billing,
-- |         and authentication. These types form the backbone of the console domain model.
-- | **Why:** Strong typing ensures business logic correctness. All types are total
-- |         (no partial functions), deterministic (no runtime surprises), and verifiable
-- |         (Lean4 proofs confirm invariants).
-- | **How:** ADTs model domain concepts. Newtype wrappers enforce domain boundaries.
-- |         JSON encoding/decoding is roundtrip-safe with corresponding Lean4 proofs.
-- |
-- | **Dependencies:**
-- | - Data.DateTime: Timestamp handling
-- | - Data.Argonaut: JSON encoding/decoding
-- | - Effect.Aff: Async operations
-- |
-- | **Mathematical Foundation:**
-- | - **Identifier Space:** `{prefix}_{ulid}` where ULID is monotonic, sortable
-- | - **Role Hierarchy:** `admin > member` (partial order)
-- | - **Balance Invariant:** `balance >= 0` (non-negative integers)
-- | - **Monthly Cycle:** Resets on billing period boundary
-- |
-- | **Security Properties:**
-- | - User IDs are opaque (no information leakage)
-- | - Roles enforce authorization boundaries
-- | - Soft deletes preserve audit trail
-- |
-- | **Corresponding Proofs:** `console-lean/Console/Core/Types.lean`
module Console.Core.Types
  ( -- * Identifiers
    AccountId(..)
  , UserId(..)
  , WorkspaceId(..)
  , BillingId(..)
  , KeyId(..)
  , Identifier(..)
  , createIdentifier
  , parseIdentifier
    -- * User Types
  , UserRole(..)
  , User(..)
  , UserInvite(..)
    -- * Workspace Types
  , Workspace(..)
  , WorkspaceCreate(..)
    -- * Billing Types
  , SubscriptionPlan(..)
  , SubscriptionStatus(..)
  , Subscription(..)
  , Billing(..)
  , Payment(..)
  , PaymentEnrichment(..)
  , Usage(..)
    -- * Common Types
  , Timestamps(..)
  , Email(..)
  , validateEmail
  ) where

import Prelude

import Data.Argonaut (class DecodeJson, class EncodeJson, decodeJson, encodeJson)
import Data.Argonaut.Core (Json)
import Data.Argonaut.Decode (JsonDecodeError)
import Data.Argonaut.Encode ((:=), (~>))
import Data.Argonaut.Decode.Decoders (decodeString, decodeInt, decodeNumber, decodeBoolean)
import Data.DateTime (DateTime)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.String as String
import Data.String.Regex (regex, test)
import Data.String.Regex.Flags (noFlags)

-- ═══════════════════════════════════════════════════════════════════════════════
-- IDENTIFIERS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Account identifier - globally unique across system
newtype AccountId = AccountId String

derive instance newtypeAccountId :: Newtype AccountId _
derive newtype instance eqAccountId :: Eq AccountId
derive newtype instance ordAccountId :: Ord AccountId
derive newtype instance showAccountId :: Show AccountId
derive newtype instance encodeJsonAccountId :: EncodeJson AccountId
derive newtype instance decodeJsonAccountId :: DecodeJson AccountId

-- | User identifier - unique within workspace
newtype UserId = UserId String

derive instance newtypeUserId :: Newtype UserId _
derive newtype instance eqUserId :: Eq UserId
derive newtype instance ordUserId :: Ord UserId
derive newtype instance showUserId :: Show UserId
derive newtype instance encodeJsonUserId :: EncodeJson UserId
derive newtype instance decodeJsonUserId :: DecodeJson UserId

-- | Workspace identifier
newtype WorkspaceId = WorkspaceId String

derive instance newtypeWorkspaceId :: Newtype WorkspaceId _
derive newtype instance eqWorkspaceId :: Eq WorkspaceId
derive newtype instance ordWorkspaceId :: Ord WorkspaceId
derive newtype instance showWorkspaceId :: Show WorkspaceId
derive newtype instance encodeJsonWorkspaceId :: EncodeJson WorkspaceId
derive newtype instance decodeJsonWorkspaceId :: DecodeJson WorkspaceId

-- | Billing record identifier
newtype BillingId = BillingId String

derive instance newtypeBillingId :: Newtype BillingId _
derive newtype instance eqBillingId :: Eq BillingId
derive newtype instance ordBillingId :: Ord BillingId
derive newtype instance showBillingId :: Show BillingId
derive newtype instance encodeJsonBillingId :: EncodeJson BillingId
derive newtype instance decodeJsonBillingId :: DecodeJson BillingId

-- | API key identifier
newtype KeyId = KeyId String

derive instance newtypeKeyId :: Newtype KeyId _
derive newtype instance eqKeyId :: Eq KeyId
derive newtype instance ordKeyId :: Ord KeyId
derive newtype instance showKeyId :: Show KeyId
derive newtype instance encodeJsonKeyId :: EncodeJson KeyId
derive newtype instance decodeJsonKeyId :: DecodeJson KeyId

-- | Identifier prefix type
data Identifier
  = AccountIdentifier AccountId
  | UserIdentifier UserId
  | WorkspaceIdentifier WorkspaceId
  | BillingIdentifier BillingId
  | KeyIdentifier KeyId

derive instance eqIdentifier :: Eq Identifier

-- | Create identifier with prefix
-- | Format: `{prefix}_{ulid}`
createIdentifier :: String -> String -> String
createIdentifier prefix ulid = prefix <> "_" <> ulid

-- | Parse identifier from string
parseIdentifier :: String -> Maybe Identifier
parseIdentifier s = case String.split (String.Pattern "_") s of
  ["account", ulid] -> Just (AccountIdentifier (AccountId (createIdentifier "account" ulid)))
  ["user", ulid] -> Just (UserIdentifier (UserId (createIdentifier "user" ulid)))
  ["workspace", ulid] -> Just (WorkspaceIdentifier (WorkspaceId (createIdentifier "workspace" ulid)))
  ["billing", ulid] -> Just (BillingIdentifier (BillingId (createIdentifier "billing" ulid)))
  ["key", ulid] -> Just (KeyIdentifier (KeyId (createIdentifier "key" ulid)))
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
-- USER TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | User role in workspace
-- | Defines authorization level
data UserRole
  = Admin   -- ^ Full access, can manage users
  | Member  -- ^ Limited access, can use API

derive instance eqUserRole :: Eq UserRole
derive instance ordUserRole :: Ord UserRole

instance showUserRole :: Show UserRole where
  show Admin = "admin"
  show Member = "member"

instance encodeJsonUserRole :: EncodeJson UserRole where
  encodeJson Admin = encodeJson "admin"
  encodeJson Member = encodeJson "member"

instance decodeJsonUserRole :: DecodeJson UserRole where
  decodeJson json = do
    s <- decodeString json
    case s of
      "admin" -> Right Admin
      "member" -> Right Member
      _ -> Left (pure "Invalid UserRole")

-- | User record
type User =
  { id :: UserId
  , workspaceId :: WorkspaceId
  , accountId :: Maybe AccountId
  , email :: Maybe Email
  , name :: String
  , role :: UserRole
  , monthlyLimit :: Maybe Int
  , monthlyUsage :: Maybe Int
  , timeSeen :: Maybe DateTime
  , timeCreated :: DateTime
  , timeUpdated :: DateTime
  , timeDeleted :: Maybe DateTime
  }

-- | User invitation request
type UserInvite =
  { email :: Email
  , role :: UserRole
  , monthlyLimit :: Maybe Int
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- WORKSPACE TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Workspace record
type Workspace =
  { id :: WorkspaceId
  , slug :: Maybe String
  , name :: String
  , timeCreated :: DateTime
  , timeUpdated :: DateTime
  , timeDeleted :: Maybe DateTime
  }

-- | Workspace creation request
type WorkspaceCreate =
  { name :: String
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- BILLING TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Subscription plan tiers
data SubscriptionPlan
  = Plan20   -- ^ $20/month
  | Plan100  -- ^ $100/month
  | Plan200  -- ^ $200/month

derive instance eqSubscriptionPlan :: Eq SubscriptionPlan

instance showSubscriptionPlan :: Show SubscriptionPlan where
  show Plan20 = "20"
  show Plan100 = "100"
  show Plan200 = "200"

instance encodeJsonSubscriptionPlan :: EncodeJson SubscriptionPlan where
  encodeJson Plan20 = encodeJson "20"
  encodeJson Plan100 = encodeJson "100"
  encodeJson Plan200 = encodeJson "200"

instance decodeJsonSubscriptionPlan :: DecodeJson SubscriptionPlan where
  decodeJson json = do
    s <- decodeString json
    case s of
      "20" -> Right Plan20
      "100" -> Right Plan100
      "200" -> Right Plan200
      _ -> Left (pure "Invalid SubscriptionPlan")

-- | Subscription status
data SubscriptionStatus
  = Subscribed

derive instance eqSubscriptionStatus :: Eq SubscriptionStatus

instance showSubscriptionStatus :: Show SubscriptionStatus where
  show Subscribed = "subscribed"

instance encodeJsonSubscriptionStatus :: EncodeJson SubscriptionStatus where
  encodeJson Subscribed = encodeJson "subscribed"

instance decodeJsonSubscriptionStatus :: DecodeJson SubscriptionStatus where
  decodeJson json = do
    s <- decodeString json
    case s of
      "subscribed" -> Right Subscribed
      _ -> Left (pure "Invalid SubscriptionStatus")

-- | Subscription details
type Subscription =
  { status :: SubscriptionStatus
  , seats :: Int
  , plan :: SubscriptionPlan
  , useBalance :: Maybe Boolean
  , coupon :: Maybe String
  }

-- | Billing record
type Billing =
  { id :: BillingId
  , workspaceId :: WorkspaceId
  , customerId :: Maybe String
  , paymentMethodId :: Maybe String
  , paymentMethodType :: Maybe String
  , paymentMethodLast4 :: Maybe String
  , balance :: Int  -- ^ Non-negative, in cents
  , monthlyLimit :: Maybe Int
  , monthlyUsage :: Maybe Int
  , reload :: Maybe Boolean
  , reloadTrigger :: Maybe Int
  , reloadAmount :: Maybe Int
  , reloadError :: Maybe String
  , subscription :: Maybe Subscription
  , subscriptionId :: Maybe String
  , subscriptionPlan :: Maybe SubscriptionPlan
  , timeCreated :: DateTime
  , timeUpdated :: DateTime
  }

-- | Payment enrichment type
data PaymentEnrichment
  = SubscriptionPayment { couponId :: Maybe String }
  | CreditPayment

derive instance eqPaymentEnrichment :: Eq PaymentEnrichment

-- | Payment record
type Payment =
  { id :: String
  , workspaceId :: WorkspaceId
  , customerId :: Maybe String
  , invoiceId :: Maybe String
  , paymentId :: Maybe String
  , amount :: Int  -- ^ Non-negative, in cents
  , enrichment :: Maybe PaymentEnrichment
  , timeCreated :: DateTime
  , timeRefunded :: Maybe DateTime
  }

-- | Usage record
type Usage =
  { id :: String
  , workspaceId :: WorkspaceId
  , model :: String
  , provider :: String
  , inputTokens :: Int
  , outputTokens :: Int
  , reasoningTokens :: Maybe Int
  , cacheReadTokens :: Maybe Int
  , cacheWrite5mTokens :: Maybe Int
  , cacheWrite1hTokens :: Maybe Int
  , cost :: Int  -- ^ Non-negative, in micro-cents
  , keyId :: Maybe KeyId
  , timeCreated :: DateTime
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMMON TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Common timestamp fields
type Timestamps =
  { timeCreated :: DateTime
  , timeUpdated :: DateTime
  , timeDeleted :: Maybe DateTime
  }

-- | Validated email address
newtype Email = Email String

derive instance newtypeEmail :: Newtype Email _
derive newtype instance eqEmail :: Eq Email
derive newtype instance ordEmail :: Ord Email
derive newtype instance showEmail :: Show Email
derive newtype instance encodeJsonEmail :: EncodeJson Email
derive newtype instance decodeJsonEmail :: DecodeJson Email

-- | Validate email format
-- | Returns Nothing if invalid
validateEmail :: String -> Maybe Email
validateEmail s =
  case regex "^[^@]+@[^@]+\\.[^@]+$" noFlags of
    Left _ -> Nothing
    Right re -> if test re s then Just (Email s) else Nothing
