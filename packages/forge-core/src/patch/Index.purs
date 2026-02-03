-- | Patch management
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/patch/index.ts
module Forge.Patch.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Patch operation
type Patch =
  { file :: String
  , oldContent :: String
  , newContent :: String
  }

-- | Apply a patch
apply :: Patch -> Aff (Either String Unit)
apply patch = notImplemented "Patch.Index.apply"

-- | Create a patch from diff
createFromDiff :: String -> String -> String -> Patch
createFromDiff file old new = { file, oldContent: old, newContent: new }

-- | Revert a patch
revert :: Patch -> Aff (Either String Unit)
revert patch = notImplemented "Patch.Index.revert"
