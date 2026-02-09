-- | Project route
-- | 1:1 parity with opencode-dev/packages/opencode/src/server/routes/project.ts
module Forge.Server.Routes.Project where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Foreign (Foreign)

-- | Get project info
get :: Aff (Either String Foreign)
get = getFFI

-- | List files in project
listFiles :: Aff (Either String (Array Foreign))
listFiles = listFilesFFI

-- | Get file tree
tree :: Int -> Aff (Either String (Array Foreign))
tree maxDepth = treeFFI maxDepth

foreign import getFFI :: Aff (Either String Foreign)
foreign import listFilesFFI :: Aff (Either String (Array Foreign))
foreign import treeFFI :: Int -> Aff (Either String (Array Foreign))
