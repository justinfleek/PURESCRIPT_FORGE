-- | Skill Index
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/skill/index.ts
module Opencode.Skill.Index where

import Opencode.Skill.Skill as Skill

-- Re-export skill functions
load :: String -> _
load = Skill.load

list :: _
list = Skill.list
