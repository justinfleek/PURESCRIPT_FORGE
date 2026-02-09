-- | PureScript type definitions for Forge Storage types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript types from forge-dev/packages/forge/src/storage/storage.ts
module Forge.Types.Storage where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe)
import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, (.:), (.:?))
import Effect.Aff (Aff)

-- | Storage key path (array of strings representing nested keys)
type StorageKey = Array String

-- | Storage operation result
data StorageResult a
  = Found a
  | NotFound
  | Error String

derive instance genericStorageResult :: Generic (StorageResult a) _
derive instance eqStorageResult :: Eq a => Eq (StorageResult a)
derive instance functorStorageResult :: Functor StorageResult

instance showStorageResult :: Show a => Show (StorageResult a) where
  show = genericShow

-- | Storage operations interface
class Storage m where
  -- | Read value from storage
  read :: forall a. DecodeJson a => StorageKey -> Aff (StorageResult a)
  
  -- | Write value to storage
  write :: forall a. EncodeJson a => StorageKey -> a -> Aff Unit
  
  -- | Delete value from storage
  delete :: StorageKey -> Aff Unit
  
  -- | List all keys under a prefix
  list :: StorageKey -> Aff (Array StorageKey)
  
  -- | Check if key exists
  exists :: StorageKey -> Aff Boolean

-- | Storage error types
data StorageError
  = NotFoundError { message :: String }
  | IOError String
  | SerializationError String

derive instance genericStorageError :: Generic StorageError _
derive instance eqStorageError :: Eq StorageError

instance showStorageError :: Show StorageError where
  show = genericShow

-- | Storage migration function
type Migration = String -> Aff Unit

-- | Storage configuration
type StorageConfig =
  { basePath :: String
  , migrations :: Array Migration
  }

derive instance genericStorageConfig :: Generic StorageConfig _
derive instance eqStorageConfig :: Eq StorageConfig

instance showStorageConfig :: Show StorageConfig where
  show = genericShow
