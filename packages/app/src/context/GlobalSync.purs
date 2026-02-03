-- | Global sync context - manages global state synchronization
-- | Migrated from: forge-dev/packages/app/src/context/global-sync.tsx
module App.Context.GlobalSync
  ( GlobalState
  , SyncStatus(..)
  , Project
  , Agent
  , Command
  , Config
  , Path
  , ProviderInfo
  , ProviderListResponse
  , ChildState
  , mkGlobalState
  , mkChildState
  , sessionRecentWindow
  , sessionRecentLimit
  , sessionUpdatedAt
  , compareSessionRecent
  , takeRecentSessions
  , trimSessions
  ) where

import Prelude

import Data.Array (filter, length, slice, sortBy, take, (:))
import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set

-- | Sync status
data SyncStatus
  = Loading
  | Partial
  | Complete

derive instance eqSyncStatus :: Eq SyncStatus

instance showSyncStatus :: Show SyncStatus where
  show Loading = "loading"
  show Partial = "partial"
  show Complete = "complete"

-- | Project info
type Project =
  { id :: String
  , worktree :: String
  , name :: Maybe String
  , sandboxes :: Array String
  , icon :: Maybe { url :: Maybe String, override :: Maybe String, color :: Maybe String }
  }

-- | Agent info
type Agent =
  { name :: String
  , mode :: Maybe String
  , hidden :: Boolean
  , model :: Maybe { providerID :: String, modelID :: String }
  }

-- | Command info
type Command =
  { name :: String
  , description :: Maybe String
  }

-- | Configuration
type Config = Map String String

-- | Path information
type Path =
  { state :: String
  , config :: String
  , worktree :: String
  , directory :: String
  , home :: String
  }

-- | Provider model info
type ModelInfo =
  { id :: String
  , name :: String
  , status :: Maybe String
  }

-- | Provider info
type ProviderInfo =
  { id :: String
  , name :: String
  , models :: Map String ModelInfo
  }

-- | Provider list response
type ProviderListResponse =
  { all :: Array ProviderInfo
  , connected :: Array ProviderInfo
  , default :: Map String String
  }

-- | Session time
type SessionTime =
  { created :: Number
  , updated :: Maybe Number
  , archived :: Maybe Number
  }

-- | Session
type Session =
  { id :: String
  , title :: Maybe String
  , parentID :: Maybe String
  , time :: SessionTime
  }

-- | Session status
type SessionStatus =
  { running :: Boolean
  , error :: Maybe String
  }

-- | File diff
type FileDiff =
  { file :: String
  , additions :: Int
  , deletions :: Int
  }

-- | Todo
type Todo =
  { id :: String
  , content :: String
  , status :: String
  }

-- | Permission request
type PermissionRequest =
  { id :: String
  , sessionID :: String
  , permission :: String
  }

-- | Question request
type QuestionRequest =
  { id :: String
  , sessionID :: String
  , question :: String
  }

-- | MCP status
type McpStatus =
  { name :: String
  , status :: String
  }

-- | LSP status
type LspStatus =
  { name :: String
  , status :: String
  }

-- | VCS info
type VcsInfo =
  { branch :: String
  }

-- | Child state (per-project)
type ChildState =
  { status :: SyncStatus
  , agent :: Array Agent
  , command :: Array Command
  , project :: String
  , projectMeta :: Maybe { name :: Maybe String, icon :: Maybe { override :: Maybe String, color :: Maybe String } }
  , icon :: Maybe String
  , provider :: ProviderListResponse
  , config :: Config
  , path :: Path
  , session :: Array Session
  , sessionTotal :: Int
  , sessionStatus :: Map String SessionStatus
  , sessionDiff :: Map String (Array FileDiff)
  , todo :: Map String (Array Todo)
  , permission :: Map String (Array PermissionRequest)
  , question :: Map String (Array QuestionRequest)
  , mcp :: Map String McpStatus
  , lsp :: Array LspStatus
  , vcs :: Maybe VcsInfo
  , limit :: Int
  }

-- | Global state
type GlobalState =
  { ready :: Boolean
  , error :: Maybe { code :: String, message :: String }
  , path :: Path
  , project :: Array Project
  , provider :: ProviderListResponse
  , providerAuth :: Map String Boolean
  , config :: Config
  , reload :: Maybe String  -- "pending" | "complete"
  }

-- | Session recent window (4 hours)
sessionRecentWindow :: Number
sessionRecentWindow = 4.0 * 60.0 * 60.0 * 1000.0

-- | Session recent limit
sessionRecentLimit :: Int
sessionRecentLimit = 50

-- | Create initial global state
mkGlobalState :: GlobalState
mkGlobalState =
  { ready: false
  , error: Nothing
  , path: { state: "", config: "", worktree: "", directory: "", home: "" }
  , project: []
  , provider: { all: [], connected: [], default: Map.empty }
  , providerAuth: Map.empty
  , config: Map.empty
  , reload: Nothing
  }

-- | Create initial child state
mkChildState :: ChildState
mkChildState =
  { status: Loading
  , agent: []
  , command: []
  , project: ""
  , projectMeta: Nothing
  , icon: Nothing
  , provider: { all: [], connected: [], default: Map.empty }
  , config: Map.empty
  , path: { state: "", config: "", worktree: "", directory: "", home: "" }
  , session: []
  , sessionTotal: 0
  , sessionStatus: Map.empty
  , sessionDiff: Map.empty
  , todo: Map.empty
  , permission: Map.empty
  , question: Map.empty
  , mcp: Map.empty
  , lsp: []
  , vcs: Nothing
  , limit: 5
  }

-- | Get session updated time
sessionUpdatedAt :: Session -> Number
sessionUpdatedAt session =
  fromMaybe session.time.created session.time.updated

-- | Compare sessions by recency
compareSessionRecent :: Session -> Session -> Ordering
compareSessionRecent a b =
  let
    aUpdated = sessionUpdatedAt a
    bUpdated = sessionUpdatedAt b
  in
    case compare bUpdated aUpdated of
      EQ -> compare a.id b.id
      other -> other

-- | Take recent sessions (not archived, sorted by recency)
takeRecentSessions :: Array Session -> Int -> Number -> Array Session
takeRecentSessions sessions limit cutoff =
  if limit <= 0
  then []
  else
    let
      sorted = sortBy compareSessionRecent sessions
      recent = filter (\s -> sessionUpdatedAt s > cutoff) sorted
      unique = dedupe recent
    in
      take limit unique
  where
    dedupe :: Array Session -> Array Session
    dedupe arr = go [] Set.empty arr
      where
        go acc _ [] = acc
        go acc seen (s : rest) =
          if Set.member s.id seen
          then go acc seen rest
          else go (Array.snoc acc s) (Set.insert s.id seen) rest

-- | Trim sessions to limit, keeping recent ones
trimSessions :: Array Session -> { limit :: Int, permission :: Map String (Array PermissionRequest) } -> Array Session
trimSessions input opts =
  let
    limit = max 0 opts.limit
    cutoff = 0.0 -- Would be Date.now() - sessionRecentWindow in real impl
    
    -- Filter out archived
    all = input
      # filter (\s -> case s.time.archived of
          Nothing -> true
          Just _ -> false)
      # sortBy (\a b -> compare a.id b.id)
    
    -- Separate roots and children
    roots = filter (\s -> s.parentID == Nothing) all
    children = filter (\s -> s.parentID /= Nothing) all
    
    -- Take base roots up to limit
    base = take limit roots
    
    -- Take recent roots from remainder
    remaining = Array.drop limit roots
    recent = takeRecentSessions remaining sessionRecentLimit cutoff
    
    keepRoots = base <> recent
    keepRootIds = Set.fromFoldable (map _.id keepRoots)
    
    -- Keep children whose parent is kept or have permissions or are recent
    keepChildren = filter (\s ->
      case s.parentID of
        Nothing -> false
        Just pid ->
          Set.member pid keepRootIds ||
          (Map.lookup s.id opts.permission # map (\p -> length p > 0) # fromMaybe false) ||
          sessionUpdatedAt s > cutoff
    ) children
  in
    sortBy (\a b -> compare a.id b.id) (keepRoots <> keepChildren)
