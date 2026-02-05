-- | Google Chunk Conversion
module Console.App.Routes.Omega.Util.Provider.Google.Chunk
  ( fromGoogleChunk
  , toGoogleChunk
  ) where

import Prelude
import Console.App.Routes.Omega.Util.Provider.Provider (CommonChunk)

fromGoogleChunk :: String -> Either String CommonChunk
fromGoogleChunk chunk = case fromGoogleChunkImpl chunk of
  { error: err } -> Left err
  result -> Right result

foreign import fromGoogleChunkImpl :: String -> { error :: String | CommonChunk }

toGoogleChunk :: CommonChunk -> String
toGoogleChunk chunk = toGoogleChunkImpl chunk

foreign import toGoogleChunkImpl :: CommonChunk -> String
