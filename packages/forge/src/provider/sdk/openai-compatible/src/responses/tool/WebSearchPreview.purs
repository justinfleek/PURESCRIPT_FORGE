-- | Web Search Preview Tool
module Forge.Provider.SDK.OpenAICompatible.Responses.Tool.WebSearchPreview where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe)

-- | Web search preview input
type WebSearchPreviewInput =
  { url :: String
  }

-- | Web search preview output
type WebSearchPreviewOutput =
  { title :: Maybe String
  , description :: Maybe String
  , content :: String
  }

foreign import previewFFI :: String -> Aff (Either String WebSearchPreviewOutput)

-- | Get preview of a URL
preview :: WebSearchPreviewInput -> Aff (Either String WebSearchPreviewOutput)
preview input = previewFFI input.url
