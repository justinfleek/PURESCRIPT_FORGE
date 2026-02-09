-- | Skills system
-- | 1:1 parity with opencode-dev/packages/opencode/src/skill/skill.ts
module Forge.Skill.Skill where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)

type Skill =
  { name :: String
  , description :: String
  , content :: String
  }

foreign import loadImpl :: String -> Aff (Either String Skill)
foreign import listImpl :: Aff (Either String (Array Skill))
foreign import getImpl :: String -> Aff (Maybe Skill)

load :: String -> Aff (Either String Skill)
load name = loadImpl name

list :: Aff (Either String (Array Skill))
list = listImpl

get :: String -> Aff (Maybe Skill)
get name = getImpl name
