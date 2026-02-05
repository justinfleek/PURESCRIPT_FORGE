{-|
Module      : Sidepanel.Components.SemanticCode.TypeInferenceTypes
Description : Types for type inference
Types for type inference and display.
-}
module Sidepanel.Components.SemanticCode.TypeInferenceTypes where

import Prelude

-- | Type information
type TypeInfo =
  { type_ :: InferredType
  , location :: { file :: String, line :: Int, column :: Int }
  , documentation :: Maybe String
  , isInferred :: Boolean  -- True if type was inferred, false if explicit
  }

-- | Inferred type
type InferredType =
  { kind :: TypeKind
  , name :: Maybe String
  , signature :: Maybe String  -- Full type signature
  , parameters :: Array InferredType  -- Type parameters
  , types :: Array InferredType  -- For union/intersection types
  }

-- | Type kind
data TypeKind
  = PrimitiveType
  | FunctionType
  | GenericType
  | UnionType
  | IntersectionType
  | ArrayType
  | ObjectType
  | UnknownType

derive instance eqTypeKind :: Eq TypeKind
