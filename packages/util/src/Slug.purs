-- | Random slug generator
-- | Migrated from opencode-dev/packages/util/src/slug.ts
module Opencode.Util.Slug
  ( create
  ) where

import Prelude
import Effect (Effect)
import Effect.Random (randomInt)
import Data.Array (index, length)
import Data.Maybe (fromMaybe)

adjectives :: Array String
adjectives =
  [ "brave", "calm", "clever", "cosmic", "crisp", "curious", "eager"
  , "gentle", "glowing", "happy", "hidden", "jolly", "kind", "lucky"
  , "mighty", "misty", "neon", "nimble", "playful", "proud", "quick"
  , "quiet", "shiny", "silent", "stellar", "sunny", "swift", "tidy", "witty"
  ]

nouns :: Array String
nouns =
  [ "cabin", "cactus", "canyon", "circuit", "comet", "eagle", "engine"
  , "falcon", "forest", "garden", "harbor", "island", "knight", "lagoon"
  , "meadow", "moon", "mountain", "nebula", "orchid", "otter", "panda"
  , "pixel", "planet", "river", "rocket", "sailor", "squid", "star"
  , "tiger", "wizard", "wolf"
  ]

create :: Effect String
create = do
  adjIdx <- randomInt 0 (length adjectives - 1)
  nounIdx <- randomInt 0 (length nouns - 1)
  let adj = fromMaybe "brave" (index adjectives adjIdx)
  let noun = fromMaybe "cabin" (index nouns nounIdx)
  pure (adj <> "-" <> noun)
