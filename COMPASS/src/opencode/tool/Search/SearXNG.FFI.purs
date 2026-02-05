{-|
Module      : Tool.Search.SearXNG.FFI
Description : HTTP FFI for SearXNG API
= SearXNG HTTP FFI

Foreign function interface for making HTTP requests to SearXNG instances.
-}
module Tool.Search.SearXNG.FFI
  ( -- * HTTP Client
    httpGet
  , httpGetWithTimeout
    -- * Types
  , HttpResponse(..)
  ) where

import Prelude

import Data.Either (Either)
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

type HttpResponse =
  { statusCode :: Int
  , headers :: Array { key :: String, value :: String }
  , body :: String
  }

-- ============================================================================
-- HTTP CLIENT
-- ============================================================================

-- | Perform HTTP GET request
foreign import httpGet :: String -> Aff (Either String HttpResponse)

-- | Perform HTTP GET request with timeout (milliseconds)
foreign import httpGetWithTimeout :: Int -> String -> Aff (Either String HttpResponse)

-- | Get current timestamp in milliseconds
foreign import nowMillis :: Effect Number

-- | Hash a string (simple hash for proof - would use crypto in production)
foreign import hashString :: String -> String
