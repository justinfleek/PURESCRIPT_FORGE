-- | Haskell validator for TypeScript type escapes
-- | Phase 2: Type Safety Layer
-- | Detects uses of type escapes that bypass type checking
module Opencode.Validator.TypeEscapes where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (listDirectory, doesFileExist, doesDirectoryExist)
import System.FilePath ((</>), takeExtension)
import Control.Monad (forM_, when)
import Data.List (isSuffixOf)

-- | Type escape pattern
data TypeEscape = TypeEscape
  { pattern :: T.Text
  , name :: String
  , description :: String
  }

-- | Known type escape patterns
typeEscapes :: [TypeEscape]
typeEscapes =
  [ TypeEscape
      { pattern = "as unknown as"
      , name = "Double type assertion"
      , description = "Type escape via double assertion - use proper type guards"
      }
  , TypeEscape
      { pattern = "as any as"
      , name = "Any type assertion"
      , description = "Type escape via any assertion - use proper types"
      }
  , TypeEscape
      { pattern = "Record<string, any>"
      , name = "Any record"
      , description = "Record with any values - use proper record types"
      }
  , TypeEscape
      { pattern = "Array<any>"
      , name = "Any array"
      , description = "Array with any elements - use proper array types"
      }
  , TypeEscape
      { pattern = "Map<string, any>"
      , name = "Any map"
      , description = "Map with any values - use proper map types"
      }
  , TypeEscape
      { pattern = "Promise<any>"
      , name = "Any promise"
      , description = "Promise with any result - use proper promise types"
      }
  ]

-- | Check a single file for type escapes
checkFile :: FilePath -> IO [(Int, TypeEscape)]
checkFile filePath = do
  content <- TIO.readFile filePath
  let lines = T.lines content
      results = concatMap (checkLine typeEscapes) (zip [1 ..] lines)
  return results
  where
    checkLine :: [TypeEscape] -> (Int, T.Text) -> [(Int, TypeEscape)]
    checkLine escapes (lineNum, line) =
      [ (lineNum, escape)
      | escape <- escapes
      , T.isInfixOf (pattern escape) line
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
                  putStrLn $ "  Line " ++ show lineNum ++ ": " ++ name escape ++ " - " ++ description escape
              else return ()
          else if isDir' && file /= "node_modules" && file /= ".git"
            then validateDirectory fullPath
            else return ()
