-- | Session Instructions
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/session/instruction.ts
module Opencode.Session.Instruction where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Instruction type
type Instruction =
  { id :: String
  , content :: String
  , priority :: Int
  , source :: String  -- "system", "user", "project"
  }

-- | Get all active instructions for a session
getInstructions :: String -> Aff (Either String (Array Instruction))
getInstructions sessionId = notImplemented "Session.Instruction.getInstructions"

-- | Add an instruction
addInstruction :: String -> Instruction -> Aff (Either String Unit)
addInstruction sessionId instruction = notImplemented "Session.Instruction.addInstruction"
