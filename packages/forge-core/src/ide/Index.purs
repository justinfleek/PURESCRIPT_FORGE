-- | IDE Integration
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/ide/index.ts
module Forge.IDE.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | IDE type
data IDEType = VSCode | Cursor | JetBrains | Vim | Emacs | Unknown

-- | Detect current IDE
detect :: Aff (Maybe IDEType)
detect = notImplemented "IDE.Index.detect"

-- | Open a file in the IDE
openFile :: String -> Maybe Int -> Aff (Either String Unit)
openFile path line = notImplemented "IDE.Index.openFile"
