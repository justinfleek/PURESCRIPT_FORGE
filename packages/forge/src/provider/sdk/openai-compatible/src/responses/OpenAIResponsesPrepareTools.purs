-- | OpenAI Responses Prepare Tools
module Forge.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesPrepareTools where

import Prelude
import Data.Maybe (Maybe)
import Foreign (Foreign)
import Forge.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesAPITypes (ToolDefinition)
-- | Prepare tools for OpenAI API format
prepareTools :: Array Foreign -> Array ToolDefinition
prepareTools _ = []
