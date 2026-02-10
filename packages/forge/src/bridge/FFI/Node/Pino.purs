-- | Pino Logger FFI - Forward Declaration
-- | Full implementation in bridge/ batch (Batch 7)
module Bridge.FFI.Node.Pino where

import Effect (Effect)

-- | Opaque Pino logger handle
foreign import data Logger :: Type

-- | Log info message
foreign import info :: Logger -> String -> Effect Unit

-- | Log error message
foreign import error :: Logger -> String -> Effect Unit

-- | Log warning message
foreign import warn :: Logger -> String -> Effect Unit

-- | Log debug message
foreign import debug :: Logger -> String -> Effect Unit
