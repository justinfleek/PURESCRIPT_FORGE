-- | Anthropic Chunk Conversion
module Console.App.Routes.Omega.Util.Provider.Anthropic.Chunk
  ( fromAnthropicChunk
  , toAnthropicChunk
  ) where

import Prelude
import Console.App.Routes.Omega.Util.Provider.Provider (CommonChunk)

fromAnthropicChunk :: String -> Either String CommonChunk
fromAnthropicChunk chunk = case fromAnthropicChunkImpl chunk of
  { error: err } -> Left err
  result -> Right result

foreign import fromAnthropicChunkImpl :: String -> { error :: String | CommonChunk }

toAnthropicChunk :: CommonChunk -> String
toAnthropicChunk chunk = toAnthropicChunkImpl chunk

foreign import toAnthropicChunkImpl :: CommonChunk -> String
