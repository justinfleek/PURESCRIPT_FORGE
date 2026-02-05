-- | OpenAI Chunk Conversion
-- | Converts streaming chunks between OpenAI format and CommonChunk
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/openai.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Provider.OpenAI.Chunk
  ( fromOpenaiChunk
  , toOpenaiChunk
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Console.App.Routes.Omega.Util.Provider.Provider (CommonChunk)

-- | Convert OpenAI chunk format to CommonChunk
fromOpenaiChunk :: String -> Either String CommonChunk
fromOpenaiChunk chunk = case fromOpenaiChunkImpl chunk of
  { error: err } -> Left err
  result -> Right result

foreign import fromOpenaiChunkImpl :: String -> { error :: String | CommonChunk }

-- | Convert CommonChunk to OpenAI chunk format
toOpenaiChunk :: CommonChunk -> String
toOpenaiChunk chunk = toOpenaiChunkImpl chunk

foreign import toOpenaiChunkImpl :: CommonChunk -> String
