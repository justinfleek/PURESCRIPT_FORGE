-- | Data Context - Session and Message Data Provider
-- |
-- | Provides access to session data, messages, parts, permissions,
-- | and questions throughout the component tree.
-- |
-- | Source: _OTHER/opencode-original/packages/ui/src/context/data.tsx
module Forge.UI.Context.Data
  ( DataContext
  , DataProvider
  , useData
  , PermissionRespondFn
  , QuestionReplyFn
  , QuestionRejectFn
  , NavigateToSessionFn
  , DataStore
  ) where

import Prelude

import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Forge.SDK.Types (Session, SessionStatus, Message, Part, FileDiff, PermissionRequest, QuestionRequest, QuestionAnswer)

-- | The data store containing all session-related data
type DataStore =
  { session :: Array Session
  , sessionStatus :: Map String SessionStatus
  , sessionDiff :: Map String (Array FileDiff)
  , sessionDiffPreload :: Maybe (Map String (Array { diff :: FileDiff }))
  , permission :: Maybe (Map String (Array PermissionRequest))
  , question :: Maybe (Map String (Array QuestionRequest))
  , message :: Map String (Array Message)
  , part :: Map String (Array Part)
  }

-- | Function to respond to permission requests
type PermissionRespondFn =
  { sessionID :: String
  , permissionID :: String
  , response :: String -- "once" | "always" | "reject"
  } -> Effect Unit

-- | Function to reply to questions
type QuestionReplyFn =
  { requestID :: String
  , answers :: Array QuestionAnswer
  } -> Effect Unit

-- | Function to reject a question
type QuestionRejectFn =
  { requestID :: String 
  } -> Effect Unit

-- | Function to navigate to a session
type NavigateToSessionFn = String -> Effect Unit

-- | Data context value
type DataContext =
  { store :: DataStore
  , directory :: String
  , respondToPermission :: Maybe PermissionRespondFn
  , replyToQuestion :: Maybe QuestionReplyFn
  , rejectQuestion :: Maybe QuestionRejectFn
  , navigateToSession :: Maybe NavigateToSessionFn
  }

-- | Internal context reference
foreign import dataContextRef :: Ref (Maybe DataContext)

-- | Provider props
type DataProviderProps =
  { data :: DataStore
  , directory :: String
  , onPermissionRespond :: Maybe PermissionRespondFn
  , onQuestionReply :: Maybe QuestionReplyFn
  , onQuestionReject :: Maybe QuestionRejectFn
  , onNavigateToSession :: Maybe NavigateToSessionFn
  }

-- | Data provider component type  
type DataProvider = DataProviderProps -> Effect Unit

-- | Use data context
useData :: Effect DataContext
useData = do
  mCtx <- Ref.read dataContextRef
  case mCtx of
    Nothing -> throw "Data context must be used within a DataProvider"
    Just ctx -> pure ctx
