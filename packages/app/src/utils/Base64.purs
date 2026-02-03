-- | Base64 decoding utilities
-- | Migrated from: forge-dev/packages/app/src/utils/base64.ts (11 lines)
module Sidepanel.Utils.Base64
  ( decode64
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Exception (try)
import Effect.Unsafe (unsafePerformEffect)

-- | Safely decode a base64 string
-- | Returns Nothing if input is undefined or decoding fails
decode64 :: Maybe String -> Maybe String
decode64 maybeValue = case maybeValue of
  Nothing -> Nothing
  Just value -> 
    -- Use FFI for actual base64 decoding
    -- In case of error, return Nothing
    case unsafePerformEffect (try (base64DecodeImpl value)) of
      Left _ -> Nothing
      Right decoded -> Just decoded

-- | Foreign import for base64 decoding
-- | Uses @forge-ai/util/encode.base64Decode
foreign import base64DecodeImpl :: String -> Effect String

-- Placeholder Effect import
foreign import data Effect :: Type -> Type
foreign import data Left :: Type -> Type
foreign import data Right :: Type -> Type
