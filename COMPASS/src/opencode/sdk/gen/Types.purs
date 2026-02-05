-- | Auto-generated from OpenAPI spec
-- | Phase 4: SDK Migration - Generated Types
module Opencode.SDK.Gen.Types where

import Prelude
import Data.Argonaut (Json, class DecodeJson, class EncodeJson, decodeJson, encodeJson, (.:), (.:?))
import Data.Maybe (Maybe)
import Data.Array (Array)

-- | Health response
type Health = { healthy :: Boolean, version :: String }

instance DecodeJson Health where
  decodeJson json = do
    obj <- decodeJson json
    healthy <- obj .: "healthy"
    version <- obj .: "version"
    pure { healthy, version }

instance EncodeJson Health where
  encodeJson h = encodeJson { healthy: h.healthy, version: h.version }

-- | Config type (from OpenAPI schema)
type Config = Json

instance DecodeJson Config where
  decodeJson = pure

instance EncodeJson Config where
  encodeJson = identity

-- | Session type (from OpenAPI schema)
type Session = Json

instance DecodeJson Session where
  decodeJson = pure

instance EncodeJson Session where
  encodeJson = identity

-- | Message type
type Message = Json

instance DecodeJson Message where
  decodeJson = pure

instance EncodeJson Message where
  encodeJson = identity

-- | Part type
type Part = Json

instance DecodeJson Part where
  decodeJson = pure

instance EncodeJson Part where
  encodeJson = identity

-- | Event type
type Event = Json

instance DecodeJson Event where
  decodeJson = pure

instance EncodeJson Event where
  encodeJson = identity
