{-# LANGUAGE OverloadedStrings #-}

-- | Haskell validator for TypeScript type escapes
-- | Phase 2: Type Safety Layer
-- | Detects uses of type escapes that bypass type checking
module Forge.Validator.TypeEscapes where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (listDirectory, doesFileExist, doesDirectoryExist)
import System.FilePath ((</>), takeExtension)
import Control.Monad (forM_, when)
import Data.List (isSuffixOf)

-- | Type escape pattern
data TypeEscape = TypeEscape
  { matchPattern :: T.Text
  , constructName :: String
  , description :: String
  }
  deriving (Show, Eq)

-- | Known type escape patterns
typeEscapes :: [TypeEscape]
typeEscapes =
  [ TypeEscape
      { matchPattern = "as unknown as"
      , constructName = "Double type assertion"
      , description = "Type escape via double assertion - use proper type guards"
      }
  , TypeEscape
      { matchPattern = "as any as"
      , constructName = "Any type assertion"
      , description = "Type escape via any assertion - use proper types"
      }
  , TypeEscape
      { matchPattern = "Record<string, any>"
      , constructName = "Any record"
      , description = "Record with any values - use proper record types"
      }
  , TypeEscape
      { matchPattern = "Array<any>"
      , constructName = "Any array"
      , description = "Array with any elements - use proper array types"
      }
  , TypeEscape
      { matchPattern = "Map<string, any>"
      , constructName = "Any map"
      , description = "Map with any values - use proper map types"
      }
  , TypeEscape
      { matchPattern = "Promise<any>"
      , constructName = "Any promise"
      , description = "Promise with any result - use proper promise types"
      }
  ]

-- | Check a single file for type escapes
checkFile :: FilePath -> IO [(Int, TypeEscape)]
checkFile filePath = do
  content <- TIO.readFile filePath
  let fileLines = T.lines content
      results = concatMap (checkLine typeEscapes) (zip [1 ..] fileLines)
  return results
  where
    checkLine :: [TypeEscape] -> (Int, T.Text) -> [(Int, TypeEscape)]
    checkLine escapes (lineNum, line) =
      [ (lineNum, escape)
      | escape <- escapes
      , T.isInfixOf (matchPattern escape) line
      ]

-- | Validate a directory for type escapes (recursive)
validateDirectory :: FilePath -> IO ()
validateDirectory dir = do
  isDir <- doesDirectoryExist dir
  if not isDir
    then putStrLn $ "Error: " ++ dir ++ " is not a directory"
    else do
      files <- listDirectory dir
      forM_ files $ \file -> do
        let fullPath = dir </> file
        isFile <- doesFileExist fullPath
        isDir' <- doesDirectoryExist fullPath
        if isFile && (takeExtension file == ".ts" || takeExtension file == ".tsx")
          then do
            violations <- checkFile fullPath
            if not (null violations)
              then do
                putStrLn $ "Type escapes found in " ++ fullPath ++ ":"
                forM_ violations $ \(lineNum, escape) ->
                  putStrLn $ "  Line " ++ show lineNum ++ ": " ++ constructName escape ++ " - " ++ description escape
              else return ()
          else if isDir' && file /= "node_modules" && file /= ".git"
            then validateDirectory fullPath
            else return ()
