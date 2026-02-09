-- | File route
-- | 1:1 parity with opencode-dev/packages/opencode/src/server/routes/file.ts
module Forge.Server.Routes.File where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))

foreign import readImpl :: String -> Aff (Either String String)
foreign import writeImpl :: String -> String -> Aff (Either String Unit)
foreign import listImpl :: String -> Aff (Either String (Array String))

read :: String -> Aff (Either String String)
read path = readImpl path

write :: String -> String -> Aff (Either String Unit)
write path content = writeImpl path content

list :: String -> Aff (Either String (Array String))
list path = listImpl path
