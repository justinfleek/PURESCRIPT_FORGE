-- | Skill Index
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/skill/index.ts
module Forge.Skill.Index where

import Forge.Skill.Skill as Skill

-- Re-export skill functions
load :: String -> _
load = Skill.load

list :: _
list = Skill.list
