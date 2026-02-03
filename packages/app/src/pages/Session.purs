-- | Session page - main chat interface with conversation display
-- | Migrated from: forge-dev/packages/app/src/pages/session.tsx (1651+ lines)
-- |
-- | This is the primary user interaction surface:
-- | - Displays conversation messages
-- | - Handles prompt input
-- | - Shows file diffs and reviews
-- | - Manages terminal integration
-- | - Handles permissions and questions
module Sidepanel.Pages.Session
  ( SessionPage
  , SessionPageState
  , SessionReviewTab
  , DiffStyle(..)
  ) where

import Prelude

import Data.Array as Array
import Data.DateTime.Instant (Instant)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Effect (Effect)
import Effect.Aff (Aff)

import Sidepanel.Context.Layout (LayoutContext)
import Sidepanel.Context.Local (LocalContext)
import Sidepanel.Context.File (FileContext, FileSelection, SelectedLineRange)
import Sidepanel.Context.Sync (SyncContext)
import Sidepanel.Context.Terminal (TerminalContext, LocalPTY)
import Sidepanel.Context.SDK (SDKContext)
import Sidepanel.Context.Prompt (PromptContext)
import Sidepanel.Context.Comments (CommentsContext, LineComment)
import Sidepanel.Context.Permission (PermissionContext)
import Sidepanel.Context.Command (CommandContext)
import Sidepanel.Context.Language (LanguageContext)

-- | Diff display style
data DiffStyle = Unified | Split

derive instance eqDiffStyle :: Eq DiffStyle

-- | File diff type
type FileDiff =
  { file :: String
  , additions :: Int
  , deletions :: Int
  }

-- | Session info type
type SessionInfo =
  { id :: String
  , title :: String
  , summary :: Maybe { files :: Int }
  , revert :: Maybe { messageID :: String }
  , share :: Maybe { url :: String }
  }

-- | Message type
type Message =
  { id :: String
  , role :: String
  , agent :: Maybe String
  , model :: Maybe String
  }

-- | User message type (subset of Message)
type UserMessage =
  { id :: String
  , role :: String
  , agent :: Maybe String
  , model :: Maybe String
  }

-- | Permission request type
type PermissionRequest =
  { id :: String
  , sessionID :: String
  , tool :: Maybe String
  }

-- | Session status type
data SessionStatus
  = Idle
  | Busy
  | Retry

-- | UI state for session page
type UIState =
  { responding :: Boolean
  , pendingMessage :: Maybe String
  , scrollGesture :: Int
  , autoCreated :: Boolean
  }

-- | Store state for session page
type StoreState =
  { activeDraggable :: Maybe String
  , activeTerminalDraggable :: Maybe String
  , expanded :: Map String Boolean
  , messageId :: Maybe String
  , turnStart :: Int
  , mobileTab :: String  -- "session" | "changes"
  , newSessionWorktree :: String
  , promptHeight :: Int
  }

-- | Tree state for file tree/review
type TreeState =
  { reviewScroll :: Maybe HTMLElement
  , pendingDiff :: Maybe String
  , activeDiff :: Maybe String
  }

-- | Combined session page state
type SessionPageState =
  { ui :: UIState
  , store :: StoreState
  , tree :: TreeState
  }

-- | Foreign HTML element type
foreign import data HTMLElement :: Type

-- | Initial UI state
initialUIState :: UIState
initialUIState =
  { responding: false
  , pendingMessage: Nothing
  , scrollGesture: 0
  , autoCreated: false
  }

-- | Initial store state
initialStoreState :: StoreState
initialStoreState =
  { activeDraggable: Nothing
  , activeTerminalDraggable: Nothing
  , expanded: Map.empty
  , messageId: Nothing
  , turnStart: 0
  , mobileTab: "session"
  , newSessionWorktree: "main"
  , promptHeight: 0
  }

-- | Initial tree state
initialTreeState :: TreeState
initialTreeState =
  { reviewScroll: Nothing
  , pendingDiff: Nothing
  , activeDiff: Nothing
  }

-- | Get session key from route params
sessionKey :: { dir :: String, id :: Maybe String } -> String
sessionKey params = params.dir <> (case params.id of
  Just id -> "/" <> id
  Nothing -> "")

-- | Get current permission request for session
getPermissionRequest :: SyncContext -> String -> Maybe PermissionRequest
getPermissionRequest sync sessionID =
  -- sync.data.permission[sessionID]?.[0] where !tool
  Nothing

-- | Handle permission decision
handlePermissionDecision :: SDKContext -> PermissionRequest -> String -> Effect Unit
handlePermissionDecision sdk request response = do
  -- sdk.client.permission.respond({ sessionID, permissionID, response })
  pure unit

-- | Get session messages
getMessages :: SyncContext -> String -> Array Message
getMessages sync sessionID =
  -- sync.data.message[sessionID] ?? []
  []

-- | Get user messages (filtered)
getUserMessages :: Array Message -> Array UserMessage
getUserMessages messages =
  Array.filter (\m -> m.role == "user") messages
    # map \m -> { id: m.id, role: m.role, agent: m.agent, model: m.model }

-- | Get visible user messages (respecting revert point)
getVisibleUserMessages :: Array UserMessage -> Maybe String -> Array UserMessage
getVisibleUserMessages messages revertMessageID =
  case revertMessageID of
    Nothing -> messages
    Just revertId -> Array.filter (\m -> m.id < revertId) messages

-- | Navigate message by offset
navigateMessageByOffset :: Int -> SessionPageState -> Array UserMessage -> Effect SessionPageState
navigateMessageByOffset offset state messages =
  let currentId = state.store.messageId
      currentIndex = case currentId of
        Nothing -> -1
        Just id -> fromMaybe (-1) $ Array.findIndex (\m -> m.id == id) messages
      targetIndex = 
        if currentIndex == -1
        then if offset > 0 then 0 else Array.length messages - 1
        else currentIndex + offset
  in if targetIndex < 0 || targetIndex >= Array.length messages
     then pure state
     else case Array.index messages targetIndex of
       Nothing -> pure state
       Just msg -> do
         -- Scroll to message, update hash
         pure state { store = state.store { messageId = Just msg.id } }

-- | Open tab in view
openTab :: LayoutContext -> String -> String -> Effect Unit
openTab layout sessionKey tabValue = do
  -- layout.tabs(sessionKey).open(tabValue)
  pure unit

-- | Normalize tab value (resolve file:// URLs)
normalizeTab :: FileContext -> String -> String
normalizeTab file tab =
  if String.take 7 tab == "file://"
  then tab  -- file.tab(tab) - resolve to actual path
  else tab

-- | Add selection to context
addSelectionToContext :: PromptContext -> FileContext -> String -> FileSelection -> Effect Unit
addSelectionToContext prompt file path selection = do
  let preview = getSelectionPreview file path selection
  -- prompt.context.add({ type: "file", path, selection, preview })
  pure unit

-- | Get preview text for selection
getSelectionPreview :: FileContext -> String -> FileSelection -> Maybe String
getSelectionPreview file path selection =
  -- Get file content, extract lines from selection
  Nothing

-- | Add comment to context
addCommentToContext :: PromptContext -> CommentsContext -> 
                       { file :: String, selection :: SelectedLineRange, comment :: String, preview :: Maybe String, origin :: Maybe String } -> 
                       Effect Unit
addCommentToContext prompt comments input = do
  -- Save comment, add to prompt context with file selection
  pure unit

-- | Handle undo (revert to previous message)
handleUndo :: SDKContext -> SyncContext -> PromptContext -> String -> SessionInfo -> Array UserMessage -> Aff Unit
handleUndo sdk sync prompt sessionID info messages = do
  -- Abort if busy
  -- Find last user message before revert point
  -- Revert to that message
  -- Restore prompt from reverted message parts
  pure unit

-- | Handle redo (unrevert or move forward)
handleRedo :: SDKContext -> SyncContext -> String -> SessionInfo -> Array UserMessage -> Aff Unit
handleRedo sdk sync sessionID info messages = do
  -- If no next message: full unrevert
  -- Otherwise: partial redo to next message
  pure unit

-- | Handle compact (summarize session)
handleCompact :: SDKContext -> LocalContext -> LanguageContext -> String -> Aff Unit
handleCompact sdk local language sessionID = do
  -- Get current model
  -- Call session.summarize
  pure unit

-- | Handle fork session
handleFork :: String -> Effect Unit
handleFork sessionID = do
  -- Show DialogFork dialog
  pure unit

-- | Handle share session
handleShare :: SDKContext -> LanguageContext -> String -> Aff Unit
handleShare sdk language sessionID = do
  -- Call session.share
  -- Copy URL to clipboard
  -- Show toast
  pure unit

-- | Handle unshare session
handleUnshare :: SDKContext -> LanguageContext -> String -> Aff Unit
handleUnshare sdk language sessionID = do
  -- Call session.unshare
  -- Show toast
  pure unit

-- | Register session commands
registerSessionCommands :: CommandContext -> LanguageContext -> String -> Maybe String -> SessionPageState -> Array _
registerSessionCommands command language dir maybeId state =
  -- Returns array of CommandOption for:
  -- - session.new
  -- - file.open
  -- - context.addSelection
  -- - terminal.toggle
  -- - review.toggle
  -- - terminal.new
  -- - steps.toggle
  -- - message.previous/next
  -- - model.choose
  -- - mcp.toggle
  -- - agent.cycle/reverse
  -- - model.variant.cycle
  -- - permissions.autoaccept
  -- - session.undo/redo
  -- - session.compact
  -- - session.fork
  -- - session.share/unshare
  []

-- | Session review tab props
type SessionReviewTabProps =
  { diffs :: Array FileDiff
  , diffStyle :: DiffStyle
  , onDiffStyleChange :: DiffStyle -> Effect Unit
  , onViewFile :: String -> Effect Unit
  , onLineComment :: { file :: String, selection :: SelectedLineRange, comment :: String, preview :: Maybe String } -> Effect Unit
  , comments :: Array LineComment
  , focusedComment :: Maybe { file :: String, id :: String }
  , onFocusedCommentChange :: Maybe { file :: String, id :: String } -> Effect Unit
  , focusedFile :: Maybe String
  , onScrollRef :: HTMLElement -> Effect Unit
  , classes :: { root :: Maybe String, header :: Maybe String, container :: Maybe String }
  }

-- | Session review tab component
-- | Shows file diffs with inline commenting
type SessionReviewTab = SessionReviewTabProps -> Effect Unit

-- | Auto-scroll hook result
type AutoScrollResult =
  { scrollRef :: HTMLElement -> Effect Unit
  , userScrolled :: Effect Boolean
  , pause :: Effect Unit
  , forceScrollToBottom :: Effect Unit
  }

-- | Turn backfill configuration
type TurnBackfillConfig =
  { turnInit :: Int      -- Initial turns to render (20)
  , turnBatch :: Int     -- Batch size for backfill (20)
  }

-- | Prefetch configuration
type PrefetchConfig =
  { chunkSize :: Int              -- 200
  , concurrency :: Int            -- 1
  , pendingLimit :: Int           -- 6
  , maxSessionsPerDir :: Int      -- 10
  }

-- | Session page component
-- |
-- | Layout:
-- | - Desktop: 
-- |   - Left: File tree / review panel (collapsible)
-- |   - Center: Chat messages
-- |   - Right: File viewer tabs
-- |   - Bottom: Terminal panel (collapsible)
-- |   - Footer: Prompt input
-- | - Mobile:
-- |   - Tab bar: session / changes
-- |   - Content area based on tab
-- |   - Prompt input
-- |
-- | Features:
-- | - Message rendering with turn grouping
-- | - Auto-scroll with gesture detection
-- | - Session prefetching
-- | - Permission/question handling
-- | - File selection and commenting
-- | - Terminal integration
-- | - Command palette commands
-- | - Drag-and-drop tabs
-- | - Deep link message navigation
type SessionPage = Effect Unit
