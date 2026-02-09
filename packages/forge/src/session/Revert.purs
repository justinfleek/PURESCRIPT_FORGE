-- | Session Revert - revert to previous state
-- | 1:1 parity with opencode-dev/packages/opencode/src/session/revert.ts
module Forge.Session.Revert where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))

type RevertResult =
  { messagesRemoved :: Int
  , revertedToId :: String
  }

foreign import revertToMessageImpl :: String -> String -> Aff (Either String RevertResult)
foreign import revertLastImpl :: String -> Int -> Aff (Either String RevertResult)
foreign import undoImpl :: String -> Aff (Either String RevertResult)

revertToMessage :: String -> String -> Aff (Either String RevertResult)
revertToMessage sessionId messageId = revertToMessageImpl sessionId messageId

revertLast :: String -> Int -> Aff (Either String RevertResult)
revertLast sessionId count = revertLastImpl sessionId count

undo :: String -> Aff (Either String RevertResult)
undo sessionId = undoImpl sessionId
