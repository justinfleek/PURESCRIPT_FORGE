-- | Named error types
-- | Migrated from opencode-dev/packages/util/src/error.ts
module Opencode.Util.Error
  ( NamedError(..)
  , UnknownError
  , mkUnknownError
  , errorName
  , errorData
  ) where

import Prelude
import Data.Generic.Rep (class Generic)

-- | A named error with typed data
data NamedError a = NamedError String a

derive instance genericNamedError :: Generic (NamedError a) _
derive instance eqNamedError :: Eq a => Eq (NamedError a)

instance showNamedError :: Show a => Show (NamedError a) where
  show (NamedError name dat) = "NamedError(" <> name <> ", " <> show dat <> ")"

-- | Get the error name
errorName :: forall a. NamedError a -> String
errorName (NamedError name _) = name

-- | Get the error data
errorData :: forall a. NamedError a -> a
errorData (NamedError _ dat) = dat

-- | Unknown error type
type UnknownError = NamedError { message :: String }

-- | Create an unknown error
mkUnknownError :: String -> UnknownError
mkUnknownError msg = NamedError "UnknownError" { message: msg }
