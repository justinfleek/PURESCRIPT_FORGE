-- | Haskell validator for file reading protocol compliance
-- | Phase 2: Type Safety Layer
-- | Ensures complete file reads only (no grep, head, tail, partial reads)
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Forge.Validator.FileReading
  ( validateDirectory
  , checkFile
  , BannedPattern(..)
  , bannedPatterns
  ) where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified System.Directory as Dir
import qualified System.FilePath as FP
import Data.List (isInfixOf)
import Control.Monad (forM, filterM)
import Control.Exception (try, SomeException)

-- | Banned file reading patterns
data BannedPattern = BannedPattern
  { matchPattern :: String
  , constructName :: String
  , reason :: String
  }

bannedPatterns :: [BannedPattern]
bannedPatterns =
  [ BannedPattern "grep" "grep" "Banned - use complete file read"
  , BannedPattern "head" "head" "Banned - use complete file read"
  , BannedPattern "tail" "tail" "Banned - use complete file read"
  , BannedPattern "readLines" "readLines" "Banned - use complete file read"
  , BannedPattern "readPartial" "readPartial" "Banned - use complete file read"
  , BannedPattern "readChunk" "readChunk" "Banned - use complete file read"
  , BannedPattern ".slice(" ".slice()" "Banned - use complete file read"
  , BannedPattern ".substring(" ".substring()" "Banned - use complete file read"
  ]

-- | Extensions to check
validExtensions :: [String]
validExtensions = [".ts", ".tsx", ".js", ".jsx", ".purs", ".hs"]

-- | Check if file has a valid extension
hasValidExtension :: FilePath -> Bool
hasValidExtension path = FP.takeExtension path `elem` validExtensions

-- | Check file for banned reading patterns
checkFile :: FilePath -> IO (Either String [String])
checkFile path = do
  result <- try $ TIO.readFile path
  case result of
    Left (err :: SomeException) -> return $ Left $ "Error reading " ++ path ++ ": " ++ show err
    Right content -> do
      let violations = findViolations content path
      return $ Right violations

-- | Find violations in file content
findViolations :: T.Text -> FilePath -> [String]
findViolations content path =
  let
    fileLines = T.lines content
    matches = zip [1 :: Int ..] fileLines
    violations = concatMap (checkPatterns path) matches
  in
    violations

-- | Check line for banned patterns
checkPatterns :: FilePath -> (Int, T.Text) -> [String]
checkPatterns path (lineNum, line) =
  let
    lineStr = T.unpack line
    matches = filter (\p -> matchPattern p `isInfixOf` lineStr) bannedPatterns
  in
    map (\p ->
      path <> ":" <> show lineNum <> ": " <> constructName p <> " - " <> reason p <> "\n  " <> lineStr
    ) matches

-- | Get all files recursively
getFilesRecursive :: FilePath -> IO [FilePath]
getFilesRecursive dir = do
  isDir <- Dir.doesDirectoryExist dir
  if not isDir
    then return []
    else do
      entries <- Dir.listDirectory dir
      let paths = map (dir FP.</>) entries
      files <- filterM Dir.doesFileExist paths
      dirs <- filterM Dir.doesDirectoryExist paths
      subFiles <- concat <$> mapM getFilesRecursive dirs
      return $ files ++ subFiles

-- | Validate directory recursively
validateDirectory :: FilePath -> IO (Either String [String])
validateDirectory dir = do
  isDir <- Dir.doesDirectoryExist dir
  if not isDir
    then return $ Left $ "Not a directory: " ++ dir
    else do
      allFiles <- getFilesRecursive dir
      let validFiles = filter hasValidExtension allFiles
      results <- forM validFiles checkFile
      case sequence results of
        Left err -> return $ Left err
        Right violations -> return $ Right $ concat violations
