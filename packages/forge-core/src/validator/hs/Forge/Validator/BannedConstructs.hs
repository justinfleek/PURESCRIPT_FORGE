-- | Haskell validator for banned TypeScript constructs
-- | Phase 2: Type Safety Layer
-- | Detects banned constructs in TypeScript code
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Forge.Validator.BannedConstructs where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified System.Directory as Dir
import qualified System.FilePath as FP
import Data.List (find)
import Control.Monad (forM_)

-- | Banned TypeScript constructs
data BannedConstruct = BannedConstruct
  { pattern :: T.Text
  , name :: String
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

-- | Check file for banned constructs
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
  concatMap (checkPattern content path) bannedConstructs

-- | Check for specific banned pattern
checkPattern :: T.Text -> FilePath -> BannedConstruct -> [String]
checkPattern content path BannedConstruct{..} =
  let
    lines' = T.lines content
    matches = zip [1..] lines'
    violations = filter (\(_, line) -> T.isInfixOf (T.pack pattern) line) matches
  in
    map (\(lineNum, line) ->
      path <> ":" <> show lineNum <> ": " <> name <> " - " <> reason <> "\n  " <> T.unpack line
    ) violations

-- | Validate directory recursively
validateDirectory :: FilePath -> IO (Either String [String])
validateDirectory dir = do
  files <- Dir.listDirectory dir
  allViolations <- mapM (checkFile . (dir FP.</>)) files
  return $ case sequence allViolations of
    Left err -> Left err
    Right violations -> Right $ concat violations
