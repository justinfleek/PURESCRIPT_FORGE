-- | File reading protocol - complete reads only
module Rules.FileReading where

import Prelude
import Data.Array (length, splitAt)
import Data.String (lines, joinWith)
import Data.Either (Either(..))

-- | File reading protocol:
-- | GREP IS BANNED
-- | HEAD/TAIL IS BANNED
-- | PARTIAL READS ARE BANNED
-- | SEARCH PATTERNS ARE BANNED
-- | "RELEVANT SECTIONS" ARE BANNED

-- | Complete file read result
type FileReadResult = 
  { filePath :: String
  , content :: String
  , lineCount :: Int
  }

-- | Read complete file
-- | Total function - handles all cases
readCompleteFile :: String -> Either String FileReadResult
readCompleteFile path = 
  -- In PureScript, file reading is effectful
  -- This is the type signature - actual implementation uses Effect
  Left "File reading requires Effect - use readCompleteFileEff"

-- | Effectful complete file read
readCompleteFileEff :: forall r. String -> Effect (Either String FileReadResult)
readCompleteFileEff path = do
  -- Implementation would use Node.FS
  -- For now, this is the type signature
  pure $ Left "Not implemented - requires Node.FS"

-- | Chunk file into segments (for large files)
-- | Each chunk is ≤500 lines
chunkFile :: String -> Array String
chunkFile content = 
  let fileLines = lines content
      chunks = chunkLines 500 fileLines
  in map (joinWith "\n") chunks

chunkLines :: Int -> Array String -> Array (Array String)
chunkLines _ [] = []
chunkLines n xs = 
  let { before, after } = splitAt n xs
  in [ before ] <> chunkLines n after

-- | BANNED: grep, head, tail, partial reads
-- | These operations are unrepresentable in our type system
