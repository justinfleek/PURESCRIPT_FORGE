-- | Feature Flags
module Opencode.Flag.Flag where

import Prelude
import Effect (Effect)
import Data.String as String
import Bridge.FFI.Node.Process (getEnv)

-- | Feature flag for auto-share
opencode_AUTO_SHARE :: Boolean
opencode_AUTO_SHARE = unsafePerformEffect $ do
  envValue <- getEnv "OPENCODE_AUTO_SHARE"
  pure $ case envValue of
    Just "true" -> true
    Just "1" -> true
    _ -> false
  where
    foreign import unsafePerformEffect :: forall a. Effect a -> a

-- | Check if a feature flag is enabled
isEnabled :: String -> Effect Boolean
isEnabled flag = do
  envValue <- getEnv ("OPENCODE_" <> String.toUpper flag)
  pure $ case envValue of
    Just "true" -> true
    Just "1" -> true
    _ -> false

-- | Get all enabled flags
getEnabled :: Effect (Array String)
getEnabled = do
  -- In production, would scan all OPENCODE_* env vars
  -- For now, return empty array
  pure []
