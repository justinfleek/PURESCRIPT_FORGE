-- | Scrap utilities (temporary/scratch data)
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/util/scrap.ts
module Forge.Util.Scrap where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Save scrap data
save :: String -> String -> Aff (Either String Unit)
save key data_ = notImplemented "Util.Scrap.save"

-- | Load scrap data
load :: String -> Aff (Either String String)
load key = notImplemented "Util.Scrap.load"

-- | Clear scrap data
clear :: String -> Aff (Either String Unit)
clear key = notImplemented "Util.Scrap.clear"
