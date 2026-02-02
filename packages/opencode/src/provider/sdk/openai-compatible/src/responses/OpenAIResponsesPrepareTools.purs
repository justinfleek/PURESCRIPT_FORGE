-- | OpenAI Responses Prepare Tools
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/provider/sdk/openai-compatible/src/responses/openai-responses-prepare-tools.ts
module Opencode.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesPrepareTools where

import Prelude
import Data.Maybe (Maybe)
import Foreign (Foreign)
import Opencode.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesAPITypes (ToolDefinition)
import Opencode.Util.NotImplemented (notImplemented)

-- | Prepare tools for OpenAI API format
prepareTools :: Array Foreign -> Array ToolDefinition
prepareTools tools = notImplemented "Responses.OpenAIResponsesPrepareTools.prepareTools"
