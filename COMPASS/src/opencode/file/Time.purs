-- | File time utilities
module Opencode.File.Time where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))

-- | File time info
type FileTime =
  { created :: Number
  , modified :: Number
  , accessed :: Number
  }

-- | Get file times
getFileTimes :: String -> Aff (Either String FileTime)
getFileTimes path = do
  result <- liftEffect $ getFileStats path
  pure $ case result of
    Left err -> Left err
    Right stats -> Right
      { created: stats.created
      , modified: stats.modified
      , accessed: stats.accessed
      }
  where
    foreign import getFileStats :: String -> Effect (Either String { created :: Number, modified :: Number, accessed :: Number })

-- | Touch a file (update modified time)
touch :: String -> Aff (Either String Unit)
touch path = do
  result <- liftEffect $ touchFile path
  pure $ case result of
    Left err -> Left err
    Right _ -> Right unit
  where
    foreign import touchFile :: String -> Effect (Either String Unit)
