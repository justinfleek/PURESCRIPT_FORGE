-- | Question handling
-- |
-- | Manages user questions and answers during tool execution.
-- |
-- | 1:1 parity with opencode-dev/packages/opencode/src/question/index.ts
module Forge.Question.Index
  ( Option
  , Info
  , Request
  , Answer
  , Reply
  , event
  , ask
  , reply
  , reject
  , list
  , rejectedError
  ) where

import Prelude
import Effect.Aff (Aff)
import Foreign (Foreign)
import Data.Maybe (Maybe)

-- | Question option
type Option =
  { label :: String
  , description :: String
  }

-- | Question info
type Info =
  { question :: String
  , header :: String
  , options :: Array Option
  , multiple :: Maybe Boolean
  , custom :: Maybe Boolean
  }

-- | Question request
type Request =
  { id :: String
  , sessionID :: String
  , questions :: Array Info
  , tool :: Maybe { messageID :: String, callID :: String }
  }

-- | Answer type (array of selected labels)
type Answer = Array String

-- | Reply with answers
type Reply =
  { answers :: Array Answer
  }

-- | Question events
foreign import event :: Foreign

-- | Ask questions
foreign import ask :: 
  { sessionID :: String
  , questions :: Array Info
  , tool :: Maybe { messageID :: String, callID :: String }
  } -> Aff (Array Answer)

-- | Reply to questions
foreign import reply :: 
  { requestID :: String
  , answers :: Array Answer
  } -> Aff Unit

-- | Reject/dismiss questions
foreign import reject :: String -> Aff Unit

-- | List pending questions
foreign import list :: Aff (Array Request)

-- | Error thrown when question is rejected
foreign import rejectedError :: Foreign
