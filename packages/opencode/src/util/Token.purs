-- | Token counting utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/util/token.ts
module Opencode.Util.Token where

import Prelude
import Opencode.Util.NotImplemented (notImplemented)

-- | Estimate token count for text
countTokens :: String -> Int
countTokens text = 0 -- TODO: Implement proper tokenization

-- | Estimate tokens for model
countTokensForModel :: String -> String -> Int
countTokensForModel model text = 0 -- TODO: Implement

-- | Truncate text to token limit
truncateToTokens :: Int -> String -> String
truncateToTokens maxTokens text = text -- TODO: Implement
