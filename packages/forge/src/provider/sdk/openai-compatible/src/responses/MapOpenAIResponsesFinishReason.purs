-- | Map OpenAI Responses Finish Reason
module Forge.Provider.SDK.OpenAICompatible.Responses.MapOpenAIResponsesFinishReason where

import Prelude

-- | Finish reason types
data FinishReason
  = Stop
  | Length
  | ToolCalls
  | ContentFilter
  | FunctionCall
  | Unknown String

-- | Map OpenAI finish reason string to our type
mapFinishReason :: String -> FinishReason
mapFinishReason "stop" = Stop
mapFinishReason "length" = Length
mapFinishReason "tool_calls" = ToolCalls
mapFinishReason "content_filter" = ContentFilter
mapFinishReason "function_call" = FunctionCall
mapFinishReason other = Unknown other
