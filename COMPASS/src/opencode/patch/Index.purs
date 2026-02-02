-- | Patch management
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/patch/index.ts
module Opencode.Patch.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

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
