-- | Slug generation utilities
-- | 1:1 parity with @opencode-ai/util/slug
module Forge.Util.Slug
  ( SlugParts
  , create
  , isValid
  , parse
  ) where

import Prelude
import Data.Maybe (Maybe)

-- | Parsed slug parts
type SlugParts =
  { adjective :: String
  , noun :: String
  , number :: Int
  }

-- | Create a new random slug
foreign import create :: Unit -> String

-- | Check if a string is a valid slug
foreign import isValid :: String -> Boolean

-- | Parse a slug into its parts
foreign import parse :: String -> Maybe SlugParts
