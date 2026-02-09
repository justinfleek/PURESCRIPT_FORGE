-- | Patch management
-- | Ported from: opencode-dev/packages/opencode/src/patch/index.ts
module Forge.Patch.Index where

import Prelude

import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | Patch definition
type Patch =
  { file :: String
  , oldContent :: String
  , newContent :: String
  }

-- | Apply a patch to a file
apply :: Patch -> Aff (Either String Unit)
apply patch = fromEffectFnAff (applyPatchFFI patch.file patch.newContent)

-- | Create a patch from old and new content
createFromDiff :: String -> String -> String -> Patch
createFromDiff file old new_ = { file, oldContent: old, newContent: new_ }

-- | Revert a patch (restore old content)
revert :: Patch -> Aff (Either String Unit)
revert patch = fromEffectFnAff (applyPatchFFI patch.file patch.oldContent)

-- | FFI: Write content to file
foreign import applyPatchFFI :: String -> String -> EffectFnAff (Either String Unit)
