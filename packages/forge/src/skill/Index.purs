-- | Skill Index
module Forge.Skill.Index where

import Forge.Skill.Skill as Skill

-- Re-export skill functions
load :: String -> _
load = Skill.load

list :: _
list = Skill.list
