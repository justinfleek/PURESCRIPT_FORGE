-- | PureScript type definitions for Forge Storage types
-- | Phase 2: Type Safety Layer
module Forge.Types.Storage where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Effect.Aff (Aff)

-- | Storage key path (array of strings representing nested keys)
type StorageKey = Array String

-- | Storage operation result
data StorageResult a
  = Found a
  | NotFound
  | StorageError String

derive instance genericStorageResult :: Generic (StorageResult a) _
derive instance eqStorageResult :: Eq a => Eq (StorageResult a)
derive instance functorStorageResult :: Functor StorageResult

instance showStorageResult :: Show a => Show (StorageResult a) where
  show = genericShow

-- | Storage error types
data StorageErrorType
  = NotFoundError String
  | IOError String
  | SerializationError String

derive instance genericStorageErrorType :: Generic StorageErrorType _
derive instance eqStorageErrorType :: Eq StorageErrorType

instance showStorageErrorType :: Show StorageErrorType where
  show = genericShow

-- | Storage configuration
type StorageConfig =
  { basePath :: String
  }
