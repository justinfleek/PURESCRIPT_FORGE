-- | Skills system
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/skill/skill.ts
module Opencode.Skill.Skill where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Skill definition
type Skill =
  { name :: String
  , description :: String
  , content :: String
  }

-- | Load a skill
load :: String -> Aff (Either String Skill)
load name = notImplemented "Skill.Skill.load"

-- | List available skills
list :: Aff (Either String (Array Skill))
list = notImplemented "Skill.Skill.list"

-- | Get skill by name
get :: String -> Aff (Maybe Skill)
get name = notImplemented "Skill.Skill.get"
