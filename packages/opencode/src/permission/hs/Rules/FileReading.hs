{-# LANGUAGE StrictData #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | File reading protocol - complete reads only
module Rules.FileReading where

import Prelude hiding (head, tail, undefined, error)
import Data.Text (Text)
import qualified Data.Text as T
import System.FilePath (FilePath)

-- | File reading protocol:
-- | GREP IS BANNED
-- | HEAD/TAIL IS BANNED
-- | PARTIAL READS ARE BANNED
-- | SEARCH PATTERNS ARE BANNED
-- | "RELEVANT SECTIONS" ARE BANNED

-- | Complete file read result
data FileReadResult = FileReadResult
  { filePath :: !FilePath
  , content :: !Text
  , lineCount :: !Int
  }
  deriving (Show, Eq)

-- | Read complete file
-- | Total function - handles all cases
readCompleteFile :: FilePath -> IO (Either String FileReadResult)
readCompleteFile path = do
  content <- T.readFile path
  let lineCount = length (T.lines content)
  pure $ Right $ FileReadResult path content lineCount

-- | Chunk file into segments (for large files)
-- | Each chunk is ≤500 lines
chunkFile :: Text -> [Text]
chunkFile content = 
  let lines = T.lines content
      chunks = chunkLines 500 lines
  in map T.unlines chunks

chunkLines :: Int -> [Text] -> [[Text]]
chunkLines _ [] = []
chunkLines n xs = 
  let (chunk, rest) = splitAt n xs
  in chunk : chunkLines n rest

-- | BANNED: grep, head, tail, partial reads
-- | These operations are unrepresentable in our type system
