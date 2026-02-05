{-|
Module      : Sidepanel.Components.Documentation.DocumentationTypes
Description : Types for documentation generation
Types for generating documentation from code.
-}
module Sidepanel.Components.Documentation.DocumentationTypes where

import Prelude

-- | Documentation
type Documentation =
  { type_ :: DocumentationType
  , content :: String  -- Generated documentation content
  , metadata :: DocumentationMetadata
  }

-- | Documentation type
data DocumentationType
  = FunctionDocumentation
  | APIDocumentation
  | READMEDocumentation
  | CommentDocumentation
  | ArchitectureDocumentation

derive instance eqDocumentationType :: Eq DocumentationType

-- | Documentation metadata
type DocumentationMetadata =
  { language :: String
  , file :: String
  }

-- | Function documentation
type FunctionDoc =
  { name :: String
  , signature :: String
  , description :: String
  , parameters :: Array ParameterDoc
  , returnType :: Maybe String
  , returnDescription :: String
  , examples :: Array String
  , throws :: Array String
  , seeAlso :: Array String
  }

-- | Parameter documentation
type ParameterDoc =
  { name :: String
  , description :: String
  , type_ :: Maybe String
  }

-- | API documentation
type APIDoc =
  { title :: String
  , description :: String
  , endpoints :: Array EndpointDoc
  , types :: Array TypeDoc
  , examples :: Array String
  }

-- | Endpoint documentation
type EndpointDoc =
  { method :: String
  , path :: String
  , description :: String
  }

-- | Type documentation
type TypeDoc =
  { name :: String
  , definition :: String
  }

-- | README documentation
type READMEDoc =
  { title :: String
  , description :: String
  , installation :: String
  , usage :: String
  , api :: String
  , examples :: String
  , contributing :: String
  , license :: String
  }

-- | Comment suggestion
type Comment =
  { location :: Location
  , text :: String
  , priority :: Int  -- 1-10, higher is more important
  }

-- | Location
type Location =
  { file :: String
  , line :: Int
  , column :: Int
  }

-- | Code element
data CodeElement
  = FunctionElement { name :: String, signature :: String, body :: String, parameters :: Array String }
  | ModuleElement String
  | ClassElement String
  | TypeElement String
  | OtherElement String

derive instance eqCodeElement :: Eq CodeElement

-- | Code context
type CodeContext =
  { language :: String
  , file :: String
  , projectRoot :: String
  , imports :: Array String
  , relatedFiles :: Array String
  }
