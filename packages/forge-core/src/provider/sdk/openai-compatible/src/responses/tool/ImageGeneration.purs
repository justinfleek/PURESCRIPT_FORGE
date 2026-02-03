-- | Image Generation Tool
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/provider/sdk/openai-compatible/src/responses/tool/image-generation.ts
module Forge.Provider.SDK.OpenAICompatible.Responses.Tool.ImageGeneration where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | Image generation input
type ImageGenerationInput =
  { prompt :: String
  , size :: Maybe String
  , quality :: Maybe String
  , style :: Maybe String
  }

-- | Image generation output
type ImageGenerationOutput =
  { url :: String
  , revisedPrompt :: Maybe String
  }

-- | Generate an image
generate :: ImageGenerationInput -> Aff (Either String ImageGenerationOutput)
generate input = notImplemented "Tool.ImageGeneration.generate"
