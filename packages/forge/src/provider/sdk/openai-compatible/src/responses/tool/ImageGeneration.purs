-- | Image Generation Tool
module Forge.Provider.SDK.OpenAICompatible.Responses.Tool.ImageGeneration where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe(..))

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

foreign import generateFFI :: String -> String -> String -> String -> Aff (Either String ImageGenerationOutput)

-- | Generate an image
generate :: ImageGenerationInput -> Aff (Either String ImageGenerationOutput)
generate input = do
  let sz = case input.size of
        Just s -> s
        Nothing -> ""
  let qual = case input.quality of
        Just q -> q
        Nothing -> ""
  let styl = case input.style of
        Just s -> s
        Nothing -> ""
  generateFFI input.prompt sz qual styl
