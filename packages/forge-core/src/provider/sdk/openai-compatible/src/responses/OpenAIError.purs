-- | OpenAI Error types
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/provider/sdk/openai-compatible/src/responses/openai-error.ts
module Forge.Provider.SDK.OpenAICompatible.Responses.OpenAIError where

import Prelude
import Data.Maybe (Maybe)

-- | OpenAI API error
type OpenAIError =
  { message :: String
  , type :: String
  , code :: Maybe String
  , param :: Maybe String
  }

-- | Error response wrapper
type OpenAIErrorResponse =
  { error :: OpenAIError
  }

-- | Parse error from response
parseError :: String -> Maybe OpenAIError
parseError _ = Nothing -- TODO: Implement JSON parsing

-- | Format error for display
formatError :: OpenAIError -> String
formatError err = err.type <> ": " <> err.message
