-- | Registry.purs - Tool registry
-- | TODO: Implement - mirrors forge/src/tool/registry.ts
module Tool.Registry where

import Prelude
import Data.Maybe (Maybe)
import Effect (Effect)

type ToolInfo = { id :: String, description :: String }

-- | Register a tool
register :: ToolInfo -> Effect Unit
register _ = notImplemented "Tool.Registry.register"

-- | Get tool by ID
get :: String -> Effect (Maybe ToolInfo)
get _ = notImplemented "Tool.Registry.get"

-- | List all registered tools
list :: Effect (Array ToolInfo)
list = notImplemented "Tool.Registry.list"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
