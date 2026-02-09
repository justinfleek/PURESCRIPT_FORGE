-- | Node.js HTTP Server FFI
module Bridge.FFI.Node.Http where

import Prelude
import Effect (Effect)

-- | Opaque HTTP Server type
foreign import data HttpServer :: Type
