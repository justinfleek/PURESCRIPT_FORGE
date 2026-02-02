-- | Haskell validator for file reading protocol compliance
-- | Phase 2: Type Safety Layer
-- | Ensures complete file reads only (no grep, head, tail, partial reads)
{-# LANGUAGE OverloadedStrings #-}

module Opencode.Validator.FileReading where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified System.Directory as Dir
import qualified System.FilePath as FP
import Data.List (isInfixOf)

-- | Banned file reading patterns
data BannedPattern = BannedPattern
  { pattern :: String
  , name :: String
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

-- | Check file for banned reading patterns
checkFile :: FilePath -> IO (Either String [String])
checkFile path = do
  content <- TIO.readFile path
  let violations = findViolations content path
  if null violations
    then return $ Right []
    else return $ Left $ unlines violations

-- | Find violations in file content
findViolations :: T.Text -> FilePath -> [String]
findViolations content path =
  let
    lines' = T.lines content
    matches = zip [1..] lines'
    violations = concatMap (checkPatterns path) matches
  in
    violations

-- | Check line for banned patterns
checkPatterns :: FilePath -> (Int, T.Text) -> [String]
checkPatterns path (lineNum, line) =
  let
    lineStr = T.unpack line
    matches = filter (\p -> pattern p `isInfixOf` lineStr) bannedPatterns
  in
    map (\p ->
      path <> ":" <> show lineNum <> ": " <> name p <> " - " <> reason p <> "\n  " <> lineStr
    ) matches

-- | Validate directory recursively
validateDirectory :: FilePath -> IO (Either String [String])
validateDirectory dir = do
  files <- Dir.listDirectory dir
  allViolations <- mapM (checkFile . (dir FP.</>)) files
  return $ case sequence allViolations of
    Left err -> Left err
    Right violations -> Right $ concat violations
