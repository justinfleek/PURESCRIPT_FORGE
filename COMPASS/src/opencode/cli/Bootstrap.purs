-- | CLI Bootstrap
module Opencode.CLI.Bootstrap where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.Filesystem as FS

-- | Bootstrap the CLI with a working directory and callback
-- | Ensures the directory exists, then runs the callback
bootstrap :: forall a. String -> Aff a -> Aff (Either String a)
bootstrap directory callback = do
  -- Check if directory exists
  exists <- FS.exists directory
  if not exists
    then do
      -- Try to create directory
      result <- FS.mkdirp directory
      case result of
        Left err -> pure $ Left ("Failed to create directory: " <> err)
        Right _ -> do
          -- Run callback
          value <- callback
          pure $ Right value
    else do
      -- Directory exists, run callback
      value <- callback
      pure $ Right value
