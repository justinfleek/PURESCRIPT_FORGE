-- | File Context FFI
module Bridge.FFI.Node.FileContext where

import Prelude
import Effect (Effect)
import Data.Either (Either)
import Data.Maybe (Maybe)
import Bridge.State.Store (StateStore)

-- | File in context
type FileInContext =
  { path :: String
  , tokens :: Int
  , readAt :: Number
  , status :: String
  , language :: String
  , size :: Int
  }

-- | Context budget
type ContextBudget =
  { used :: Int
  , total :: Int
  }

-- | File context add response
type FileContextAddResponse =
  { success :: Boolean
  , tokens :: Int
  , contextBudget :: ContextBudget
  }

-- | File context list response
type FileContextListResponse =
  { files :: Array FileInContext
  , contextBudget :: ContextBudget
  }

-- | Add file to context
foreign import addFileToContext :: StateStore -> String -> Maybe String -> Effect (Either String FileContextAddResponse)

-- | Get context files
foreign import getContextFiles :: StateStore -> Maybe String -> Maybe String -> Effect FileContextListResponse

-- | Read file content
foreign import readFileContent :: String -> Effect (Either String String)