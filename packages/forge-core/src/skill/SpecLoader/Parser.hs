{-# LANGUAGE StrictData #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Parse spec files - complete reads only
module SpecLoader.Parser where

import Prelude hiding (head, tail, undefined, error)
import Control.Monad (forM)
import Data.Maybe (Maybe(..), mapMaybe, catMaybes)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Text.Read (readMaybe)
import qualified System.Directory as Dir
import qualified System.FilePath as FP
import SpecLoader.Types (SpecFile(..), SpecSuite(..), LoadResult(..))

-- | Load all spec files from directory
-- | COMPLETE READS ONLY - no grep, no partial reads
loadSpecSuite :: FilePath -> IO LoadResult
loadSpecSuite basePath = do
  files <- Dir.listDirectory basePath
  let specFiles = filter (\f -> FP.takeExtension f == ".md") files
      numberedFiles = mapMaybe parseSpecNumber specFiles
  
  -- Read ALL files completely
  specs <- forM numberedFiles $ \(num, path) -> do
    fullPath <- pure $ basePath FP.</> path
    exists <- Dir.doesFileExist fullPath
    if exists
      then do
        -- COMPLETE FILE READ - no grep, no partial
        content <- TIO.readFile fullPath
        let lineCount = length (T.lines content)
        pure $ Just $ SpecFile
          { specNumber = num
          , specName = T.pack $ FP.takeBaseName path
          , specPath = fullPath
          , specContent = content
          , specLineCount = lineCount
          }
      else pure Nothing
  
  let validSpecs = catMaybes specs
      index = Map.fromList [(specNumber s, s) | s <- validSpecs]
  
  pure $ LoadSuccess SpecSuite
    { suiteIndex = index
    , suiteTotal = length validSpecs
    , suiteBasePath = basePath
    }

-- | Parse spec number from filename (e.g., "01-EXECUTIVE-SUMMARY.md" -> 1)
parseSpecNumber :: FilePath -> Maybe (Int, FilePath)
parseSpecNumber path =
  case T.splitOn "-" (T.pack path) of
    (numStr : _) ->
      case readMaybe (T.unpack numStr) of
        Just num -> Just (num, path)
        Nothing -> Nothing
    _ -> Nothing

-- | Note: Using System.FilePath.takeBaseName instead

-- | Helper: readMaybe
readMaybe :: Read a => String -> Maybe a
readMaybe s = case reads s of
  [(x, "")] -> Just x
  _ -> Nothing

-- | Helper: catMaybes
catMaybes :: [Maybe a] -> [a]
catMaybes = foldr (\m acc -> case m of Just x -> x : acc; Nothing -> acc) []
