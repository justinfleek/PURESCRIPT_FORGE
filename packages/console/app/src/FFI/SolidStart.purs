-- | SolidJS Start FFI Bindings
-- |
-- | Foreign function interface for SolidJS Start server API.
-- | Provides bindings for APIEvent, Response, redirect, etc.
-- |
-- | Source: SolidJS Start API
-- | Created: 2026-02-04
module Console.App.FFI.SolidStart
  ( APIEvent
  , Response
  , Request
  , URL
  , URLSearchParams
  , Locals
  , redirect
  , jsonResponse
  , textResponse
  , getRequest
  , getRequestUrl
  , getSearchParams
  , getHeader
  , setLocals
  , getLocals
  ) where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Data.Maybe (Maybe)

-- | Opaque APIEvent type from SolidJS Start
foreign import data APIEvent :: Type

-- | Opaque Response type
foreign import data Response :: Type

-- | Opaque Request type
foreign import data Request :: Type

-- | Opaque URL type
foreign import data URL :: Type

-- | Opaque URLSearchParams type
foreign import data URLSearchParams :: Type

-- | Opaque Locals type (request locals)
foreign import data Locals :: Type

-- | FFI: Create redirect response
foreign import redirect :: String -> Aff Response

-- | FFI: Create JSON response
foreign import jsonResponse :: String -> Aff Response

-- | FFI: Create text response with status
foreign import textResponse :: String -> Int -> Aff Response

-- | FFI: Get request from APIEvent
foreign import getRequest :: APIEvent -> Effect Request

-- | FFI: Get URL from request
foreign import getRequestUrl :: Request -> Effect URL

-- | FFI: Get search params from URL
foreign import getSearchParams :: URL -> Effect URLSearchParams

-- | FFI: Get header value from request
foreign import getHeader :: Request -> String -> Effect (Maybe String)

-- | FFI: Set locals value
foreign import setLocals :: APIEvent -> String -> String -> Effect Unit

-- | FFI: Get locals value
foreign import getLocals :: APIEvent -> String -> Effect (Maybe String)

-- | FFI: Get search param value
foreign import getSearchParam :: URLSearchParams -> String -> Effect (Maybe String)

-- | FFI: Create URL from string
foreign import createURL :: String -> Effect URL
