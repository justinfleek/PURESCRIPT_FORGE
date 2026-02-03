-- | OpenAI Responses Prepare Tools
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/provider/sdk/openai-compatible/src/responses/openai-responses-prepare-tools.ts
module Forge.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesPrepareTools where

import Prelude
import Data.Maybe (Maybe)
import Foreign (Foreign)
import Forge.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesAPITypes (ToolDefinition)
import Forge.Util.NotImplemented (notImplemented)

-- | Prepare tools for OpenAI API format
prepareTools :: Array Foreign -> Array ToolDefinition
prepareTools tools = notImplemented "Responses.OpenAIResponsesPrepareTools.prepareTools"
