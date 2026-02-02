-- | File ignore patterns
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/file/ignore.ts
module Opencode.File.Ignore where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Check if file should be ignored
shouldIgnore :: String -> Array String -> Boolean
shouldIgnore path patterns = false -- TODO: Implement

-- | Load .gitignore patterns
loadGitignore :: String -> Aff (Either String (Array String))
loadGitignore directory = notImplemented "File.Ignore.loadGitignore"

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
