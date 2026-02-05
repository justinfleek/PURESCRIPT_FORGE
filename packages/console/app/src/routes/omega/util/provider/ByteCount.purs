-- | Byte Counting Utilities
-- | Provides UTF-8 byte counting for accurate token usage tracking
-- |
-- | Single-byte precision enables accurate billing and usage tracking
-- | beyond token-level granularity
module Console.App.Routes.Omega.Util.Provider.ByteCount
  ( countBytes
  , countBytesInMessage
  , countBytesInMessages
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Console.App.Routes.Omega.Util.Provider.Provider (CommonMessage, CommonContentPart)

-- | Count UTF-8 bytes in a string
-- | Uses FFI for accurate UTF-8 encoding byte counting
foreign import countBytes :: String -> Int

-- | Count bytes in a single message's text content
countBytesInMessage :: CommonMessage -> Int
countBytesInMessage msg = do
  let contentBytes = case msg.content of
        Just text -> countBytes text
        Nothing -> 0
  let partsBytes = case msg.contentParts of
        Just parts -> foldl (\acc part -> acc + countBytesInPart part) 0 parts
        Nothing -> 0
  let toolCallsBytes = case msg.toolCalls of
        Just calls -> foldl (\acc call -> acc + countBytes call.functionArguments) 0 calls
        Nothing -> 0
  contentBytes + partsBytes + toolCallsBytes

-- | Count bytes in an array of messages
countBytesInMessages :: Array CommonMessage -> Int
countBytesInMessages messages = foldl (\acc msg -> acc + countBytesInMessage msg) 0 messages

-- | Count bytes in a content part
countBytesInPart :: CommonContentPart -> Int
countBytesInPart part = case part.text of
  Just text -> countBytes text
  Nothing -> 0
