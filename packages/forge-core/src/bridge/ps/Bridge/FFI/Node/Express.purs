-- | Express.js FFI bindings
module Bridge.FFI.Node.Express where

import Prelude
import Effect (Effect)
import Data.Either (Either)

-- | Opaque Express App type
foreign import data ExpressApp :: Type

-- | Opaque HTTP Server type
foreign import data HttpServer :: Type

-- | Opaque Request type
foreign import data Request :: Type

-- | Opaque Response type
foreign import data Response :: Type

-- | Create Express app
foreign import createApp :: Effect ExpressApp

-- | Create HTTP server from Express app
foreign import createServer :: ExpressApp -> Effect HttpServer

-- | Listen on port and host
foreign import listen :: HttpServer -> Int -> String -> Effect Unit -> Effect Unit

-- | GET route handler
foreign import get :: ExpressApp -> String -> (Request -> Response -> Effect Unit) -> Effect Unit

-- | Use static files
foreign import useStatic :: ExpressApp -> String -> Effect Unit

-- | Send JSON response
foreign import sendJson :: Response -> String -> Effect Unit

-- | Send file response
foreign import sendFile :: Response -> String -> String -> Effect Unit

-- | Get request path
foreign import getPath :: Request -> Effect String

-- | Get request method
foreign import getMethod :: Request -> Effect String
