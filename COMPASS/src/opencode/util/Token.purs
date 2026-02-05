-- | Token counting utilities
module Opencode.Util.Token where

import Prelude
import Data.Int as Int
import Data.String as String
import Data.Number as Number
import Data.Maybe (Maybe(..), fromMaybe)

-- | Average characters per token (approximation)
charsPerToken :: Number
charsPerToken = 4.0

-- | Estimate token count for text
-- | Uses simple character-based estimation: ~4 characters per token
countTokens :: String -> Int
countTokens text =
  let charCount = String.length text
      tokenEstimate = Number.floor (Int.toNumber charCount / charsPerToken)
  in fromMaybe 0 (Int.fromNumber tokenEstimate)

-- | Estimate tokens for model
-- | For now, uses same estimation for all models
-- | In production, would use model-specific tokenizers
countTokensForModel :: String -> String -> Int
countTokensForModel _model text = countTokens text

-- | Truncate text to token limit
-- | Estimates tokens and truncates to fit within limit
truncateToTokens :: Int -> String -> String
truncateToTokens maxTokens text =
  let maxChars = Int.toNumber maxTokens * charsPerToken
      maxCharsInt = fromMaybe (maxTokens * 4) (Int.fromNumber maxChars)
  in String.take maxCharsInt text
