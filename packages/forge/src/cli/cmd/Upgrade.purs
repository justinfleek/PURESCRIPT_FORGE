-- | Upgrade command
module Forge.CLI.Cmd.Upgrade where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe(..))

type UpgradeArgs =
  { version :: Maybe String
  , force :: Boolean
  , check :: Boolean
  }

foreign import upgradeFFI :: String -> Boolean -> Boolean -> Aff (Either String Unit)

-- | Execute the upgrade command
execute :: UpgradeArgs -> Aff (Either String Unit)
execute args = do
  let ver = case args.version of
        Just v -> v
        Nothing -> ""
  upgradeFFI ver args.force args.check
