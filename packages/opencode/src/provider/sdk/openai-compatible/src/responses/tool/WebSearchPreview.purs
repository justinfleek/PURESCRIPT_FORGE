-- | Web Search Preview Tool
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/provider/sdk/openai-compatible/src/responses/tool/web-search-preview.ts
module Opencode.Provider.SDK.OpenAICompatible.Responses.Tool.WebSearchPreview where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

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

-- | Get preview of a URL
preview :: WebSearchPreviewInput -> Aff (Either String WebSearchPreviewOutput)
preview input = notImplemented "Tool.WebSearchPreview.preview"
