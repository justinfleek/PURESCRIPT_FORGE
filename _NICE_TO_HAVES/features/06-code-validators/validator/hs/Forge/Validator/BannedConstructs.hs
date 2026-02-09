-- | Haskell validator for banned TypeScript constructs
-- | Phase 2: Type Safety Layer
-- | Detects banned constructs in TypeScript code
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Forge.Validator.BannedConstructs
  ( validateDirectory
  , checkFile
  , BannedConstruct(..)
  , bannedConstructs
  ) where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified System.Directory as Dir
import qualified System.FilePath as FP
import Control.Monad (forM, filterM)
import Control.Exception (try, SomeException)

-- | Banned TypeScript constructs
data BannedConstruct = BannedConstruct
  { matchPattern :: T.Text
  , constructName :: String
  , reason :: String
  }

bannedConstructs :: [BannedConstruct]
bannedConstructs =
  [ BannedConstruct "\\bany\\b" "any" "Type escape - use proper types"
  , BannedConstruct "\\bunknown\\b" "unknown" "Type escape - use type guards"
  , BannedConstruct "as\\s+[A-Z]" "as Type" "Type assertion - use type guards"
  , BannedConstruct "\\!\\s*[^=]" "!" "Non-null assertion - use explicit checks"
  , BannedConstruct "\\?\\?" "??" "Nullish coalescing - use explicit checks"
  , BannedConstruct "\\|\\|\\s*[^|]" "||" "Logical OR for defaults - use explicit checks"
  , BannedConstruct "@ts-ignore" "@ts-ignore" "Type ignore - fix the type"
  , BannedConstruct "@ts-expect-error" "@ts-expect-error" "Type expect error - fix the type"
  , BannedConstruct "\\beval\\s*\\(" "eval()" "Runtime evaluation - banned"
  , BannedConstruct "\\bFunction\\s*\\(" "Function()" "Runtime evaluation - banned"
  ]

-- | Extensions to check
validExtensions :: [String]
validExtensions = [".ts", ".tsx", ".js", ".jsx", ".purs", ".hs"]

-- | Check if file has a valid extension
hasValidExtension :: FilePath -> Bool
hasValidExtension path = FP.takeExtension path `elem` validExtensions

-- | Check file for banned constructs
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
  concatMap (checkPattern content path) bannedConstructs

-- | Check for specific banned pattern
checkPattern :: T.Text -> FilePath -> BannedConstruct -> [String]
checkPattern content path BannedConstruct{..} =
  let
    fileLines = T.lines content
    matches = zip [1 :: Int ..] fileLines
    violations = filter (\(_, line) -> T.isInfixOf matchPattern line) matches
  in
    map (\(lineNum, line) ->
      path <> ":" <> show lineNum <> ": " <> constructName <> " - " <> reason <> "\n  " <> T.unpack line
    ) violations

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
