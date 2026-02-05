-- | File ignore patterns
module Opencode.File.Ignore where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Tool.ASTEdit.FFI.FileIO (readFile)
import Opencode.Util.Wildcard as Wildcard

-- | Check if file should be ignored
shouldIgnore :: String -> Array String -> Boolean
shouldIgnore path patterns =
  Array.any (\pattern -> Wildcard.match pattern path) patterns

-- | Load .gitignore patterns
loadGitignore :: String -> Aff (Either String (Array String))
loadGitignore directory = do
  let gitignorePath = directory <> "/.gitignore"
  readResult <- readFile gitignorePath
  case readResult of
    Left _ -> pure $ Right []  -- .gitignore doesn't exist, return empty
    Right content -> do
      let lines = String.split (String.Pattern "\n") content
      let patterns = Array.filter (not <<< String.null) $
            Array.map String.trim $
            Array.filter (\line -> not (String.startsWith (String.Pattern "#") line)) lines
      pure $ Right patterns

-- | Default ignore patterns
defaultPatterns :: Array String
defaultPatterns = 
  [ "node_modules"
  , ".git"
  , "dist"
  , "build"
  , ".next"
  , "*.log"
  ]
