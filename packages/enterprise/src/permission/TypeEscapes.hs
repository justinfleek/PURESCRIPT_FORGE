-- | Haskell validator for TypeScript type escapes
-- | Phase 2: Type Safety Layer
-- | Detects uses of type escapes that bypass type checking
module Permission.TypeEscapes where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (listDirectory, doesFileExist, doesDirectoryExist)
import System.FilePath ((</>), takeExtension)
import Control.Monad (forM_)

-- | Type escape pattern
data TypeEscape = TypeEscape
  { tePattern :: T.Text
  , teName :: String
  , teDescription :: String
  }

-- | Known type escape patterns
typeEscapes :: [TypeEscape]
typeEscapes =
  [ TypeEscape
      { tePattern = "as unknown as"
      , teName = "Double type assertion"
      , teDescription = "Type escape via double assertion - use proper type guards"
      }
  , TypeEscape
      { tePattern = "as any as"
      , teName = "Any type assertion"
      , teDescription = "Type escape via any assertion - use proper types"
      }
  , TypeEscape
      { tePattern = "Record<string, any>"
      , teName = "Any record"
      , teDescription = "Record with any values - use proper record types"
      }
  , TypeEscape
      { tePattern = "Array<any>"
      , teName = "Any array"
      , teDescription = "Array with any elements - use proper array types"
      }
  , TypeEscape
      { tePattern = "Map<string, any>"
      , teName = "Any map"
      , teDescription = "Map with any values - use proper map types"
      }
  , TypeEscape
      { tePattern = "Promise<any>"
      , teName = "Any promise"
      , teDescription = "Promise with any result - use proper promise types"
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
      , T.isInfixOf (tePattern escape) line
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
                  putStrLn $ "  Line " ++ show lineNum ++ ": " ++ teName escape ++ " - " ++ teDescription escape
              else return ()
          else if isDir' && file /= "node_modules" && file /= ".git"
            then validateDirectory fullPath
            else return ()
