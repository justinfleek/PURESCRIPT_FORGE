-- | OpenAI-Compatible Chunk Conversion
module Console.App.Routes.Omega.Util.Provider.OpenAICompatible.Chunk
  ( fromOaCompatibleChunk
  , toOaCompatibleChunk
  ) where

import Prelude
import Console.App.Routes.Omega.Util.Provider.Provider (CommonChunk)

fromOaCompatibleChunk :: String -> Either String CommonChunk
fromOaCompatibleChunk chunk = case fromOaCompatibleChunkImpl chunk of
  { error: err } -> Left err
  result -> Right result

foreign import fromOaCompatibleChunkImpl :: String -> { error :: String | CommonChunk }

toOaCompatibleChunk :: CommonChunk -> String
toOaCompatibleChunk chunk = toOaCompatibleChunkImpl chunk

foreign import toOaCompatibleChunkImpl :: CommonChunk -> String
