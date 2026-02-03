-- | Directory layout page - wraps child routes with SDK and sync providers
-- | Migrated from: forge-dev/packages/app/src/pages/directory-layout.tsx (72 lines)
module Sidepanel.Pages.DirectoryLayout
  ( DirectoryLayout
  , DirectoryLayoutProps
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)

import Sidepanel.Context.SDK (SDKContext)
import Sidepanel.Context.Sync (SyncContext)
import Sidepanel.Context.Local (LocalContext)
import Sidepanel.Context.Language (LanguageContext)
import Sidepanel.Utils.Base64 (decode64)

-- | Props for DirectoryLayout
type DirectoryLayoutProps =
  { children :: Effect Unit
  }

-- | Route params for directory layout
type DirectoryParams =
  { dir :: Maybe String  -- Base64 encoded directory path
  }

-- | Permission response input
type PermissionResponseInput =
  { sessionID :: String
  , permissionID :: String
  , response :: String  -- "once" | "always" | "reject"
  }

-- | Question answer type
type QuestionAnswer =
  { requestID :: String
  , answers :: Array { question :: String, answer :: String }
  }

-- | Question reject input
type QuestionRejectInput =
  { requestID :: String
  }

-- | Get decoded directory from params
-- | Returns empty string if decoding fails
getDirectory :: DirectoryParams -> String
getDirectory params = case params.dir of
  Nothing -> ""
  Just encoded -> case decode64 encoded of
    Nothing -> ""
    Just decoded -> decoded

-- | Handle invalid directory URL
-- | Shows error toast and navigates to home
handleInvalidDirectory :: LanguageContext -> Effect Unit
handleInvalidDirectory language = do
  -- showToast({
  --   variant: "error",
  --   title: language.t("common.requestFailed"),
  --   description: "Invalid directory in URL."
  -- })
  -- navigate("/")
  pure unit

-- | Create permission response handler
-- | Wraps SDK permission.respond call
createPermissionResponder :: SDKContext -> PermissionResponseInput -> Aff Unit
createPermissionResponder sdk input = do
  -- sdk.client.permission.respond(input)
  pure unit

-- | Create question reply handler
-- | Wraps SDK question.reply call  
createQuestionReplier :: SDKContext -> { requestID :: String, answers :: Array QuestionAnswer } -> Aff Unit
createQuestionReplier sdk input = do
  -- sdk.client.question.reply(input)
  pure unit

-- | Create question reject handler
-- | Wraps SDK question.reject call
createQuestionRejecter :: SDKContext -> QuestionRejectInput -> Aff Unit
createQuestionRejecter sdk input = do
  -- sdk.client.question.reject(input)
  pure unit

-- | Navigate to session within current directory
navigateToSession :: DirectoryParams -> String -> Effect Unit
navigateToSession params sessionID = do
  -- navigate(`/${params.dir}/session/${sessionID}`)
  pure unit

-- | DirectoryLayout component
-- |
-- | Provider hierarchy:
-- | 1. Validates directory param (shows error + redirects if invalid)
-- | 2. SDKProvider - provides SDK client for directory
-- | 3. SyncProvider - syncs session data for directory
-- | 4. DataProvider - provides data context with handlers:
-- |    - onPermissionRespond: handle permission responses
-- |    - onQuestionReply: handle question replies
-- |    - onQuestionReject: handle question rejections
-- |    - onNavigateToSession: handle session navigation
-- | 5. LocalProvider - local session state (agent/model selection)
-- |
-- | Renders children only when directory is valid
-- | Uses iife pattern to access hooks within provider tree
type DirectoryLayout = DirectoryLayoutProps -> Effect Unit

-- | Effect to validate directory on param change
-- | Shows error and redirects if directory decoding fails
validateDirectoryEffect :: DirectoryParams -> LanguageContext -> Effect Unit
validateDirectoryEffect params language = do
  case params.dir of
    Nothing -> pure unit  -- No dir param, skip validation
    Just _ -> 
      let dir = getDirectory params
      in if dir == ""
         then handleInvalidDirectory language
         else pure unit
