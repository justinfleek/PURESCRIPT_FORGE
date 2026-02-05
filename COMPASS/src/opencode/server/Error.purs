-- | Server Error handling
module Opencode.Server.Error where

import Prelude
import Data.Maybe (Maybe)

-- | Server error type
type ServerError =
  { code :: String
  , message :: String
  , statusCode :: Int
  , data :: Maybe String
  }

-- | Create a bad request error
badRequest :: String -> ServerError
badRequest msg = { code: "BAD_REQUEST", message: msg, statusCode: 400, data: Nothing }

-- | Create an unauthorized error
unauthorized :: String -> ServerError
unauthorized msg = { code: "UNAUTHORIZED", message: msg, statusCode: 401, data: Nothing }

-- | Create a not found error
notFound :: String -> ServerError
notFound msg = { code: "NOT_FOUND", message: msg, statusCode: 404, data: Nothing }

-- | Create an internal error
internal :: String -> ServerError
internal msg = { code: "INTERNAL_ERROR", message: msg, statusCode: 500, data: Nothing }
