-- | Session Processor - orchestrates LLM interaction and tool execution
-- |
-- | This module implements the core processing loop that handles
-- | streaming LLM responses, tool calls, retries, and error handling.
-- |
-- | 1:1 parity with opencode-dev/packages/opencode/src/session/processor.ts
module Forge.Session.Processor
  ( Info
  , Result
  , CreateInput
  , create
  , doomLoopThreshold
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Maybe (Maybe)
import Foreign (Foreign)

import Forge.Session.LLM (StreamInput)

-- | Doom loop threshold - if same tool called 3 times with same input, ask permission
doomLoopThreshold :: Int
doomLoopThreshold = 3

-- | Input for creating a processor
type CreateInput =
  { assistantMessage :: Foreign  -- MessageV2.Assistant
  , sessionID :: String
  , model :: Foreign             -- Provider.Model
  , abort :: Foreign             -- AbortSignal
  }

-- | Processor info returned by create
-- | Contains the message getter, partFromToolCall lookup, and process function
type Info = Foreign

-- | Result of processing - "compact" | "stop" | "continue"
type Result = String

-- | Create a new session processor
-- | 1:1 with SessionProcessor.create in processor.ts
-- |
-- | Returns an object with:
-- | - message: getter for the assistant message
-- | - partFromToolCall(toolCallID): lookup tool part by ID
-- | - process(streamInput): run the processing loop
foreign import create :: CreateInput -> Info
