-- | Session LLM - language model interaction
-- |
-- | This module handles communication with language model providers.
-- | It wraps the Vercel AI SDK's streamText function via FFI.
-- |
-- | 1:1 parity with opencode-dev/packages/opencode/src/session/llm.ts
module Forge.Session.LLM
  ( StreamInput
  , StreamOutput
  , stream
  , hasToolCalls
  , outputTokenMax
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- | Maximum output tokens (from flag or default 32000)
foreign import outputTokenMax :: Int

-- | Alias for OUTPUT_TOKEN_MAX - use outputTokenMax directly
-- | PureScript values must be lowercase
outputTokenMaxConstant :: Int
outputTokenMaxConstant = outputTokenMax

-- | Input for LLM streaming
-- | Matches LLM.StreamInput in llm.ts
type StreamInput =
  { user :: Foreign           -- MessageV2.User
  , sessionID :: String
  , model :: Foreign          -- Provider.Model
  , agent :: Foreign          -- Agent.Info
  , system :: Array String
  , abort :: Foreign          -- AbortSignal
  , messages :: Array Foreign -- ModelMessage[]
  , small :: Maybe Boolean
  , tools :: Foreign          -- Record<string, Tool>
  , retries :: Maybe Int
  }

-- | Output from LLM streaming
-- | Matches StreamTextResult<ToolSet, unknown> in llm.ts
type StreamOutput = Foreign

-- | Stream a completion from the LLM
-- | 1:1 with LLM.stream in llm.ts
-- |
-- | This FFI call:
-- | 1. Gets provider, config, auth in parallel
-- | 2. Builds system prompts
-- | 3. Transforms params via plugins
-- | 4. Resolves tools (filters disabled)
-- | 5. Calls streamText from ai package
foreign import stream :: StreamInput -> Aff StreamOutput

-- | Check if messages contain tool-call content
-- | 1:1 with LLM.hasToolCalls in llm.ts
-- |
-- | Used to determine if a dummy tool should be added for LiteLLM proxy compatibility
foreign import hasToolCalls :: Array Foreign -> Boolean
