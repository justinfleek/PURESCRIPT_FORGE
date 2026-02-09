-- | Convert to OpenAI Responses Input
module Forge.Provider.SDK.OpenAICompatible.Responses.ConvertToOpenAIResponsesInput where

import Prelude
import Data.Maybe (Maybe)
import Foreign (Foreign)
-- | Convert internal format to OpenAI API format
convertToOpenAIInput :: Foreign -> Foreign
convertToOpenAIInput input = input
