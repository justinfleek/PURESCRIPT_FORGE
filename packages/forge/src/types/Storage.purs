-- | PureScript type definitions for OpenCode Storage types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript types from opencode-dev/packages/opencode/src/storage/storage.ts
module Opencode.Types.Storage where

import Prelude

import Data.Argonaut (class EncodeJson, class DecodeJson)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Effect.Aff (Aff)

-- | Storage key path (array of strings representing nested keys)
type StorageKey = Array String

-- | Storage operation result
data StorageResult a
  = Found a
  | NotFound
  | StorageErr String

derive instance genericStorageResult :: Generic (StorageResult a) _
derive instance eqStorageResult :: Eq a => Eq (StorageResult a)
derive instance functorStorageResult :: Functor StorageResult

instance showStorageResult :: Show a => Show (StorageResult a) where
  show = genericShow

-- | Storage operations interface
class Storage m where
  -- | Read value from storage
  readStorage :: forall a. DecodeJson a => StorageKey -> Aff (StorageResult a)

  -- | Write value to storage
  writeStorage :: forall a. EncodeJson a => StorageKey -> a -> Aff Unit

  -- | Delete value from storage
  deleteStorage :: StorageKey -> Aff Unit

  -- | List all keys under a prefix
  listKeys :: StorageKey -> Aff (Array StorageKey)

  -- | Check if key exists
  existsKey :: StorageKey -> Aff Boolean

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
