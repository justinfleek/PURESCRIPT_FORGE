{-|
Module      : Tool.ASTEdit.Types
Description : Core types for unified editing system
= ASTEdit Type System

Core types shared across all editing modes.

== Edit Modes

@
  data EditMode where
    Structural : Language → EditMode    -- AST transformations
    Text       : EditMode               -- String replacement
    Patch      : EditMode               -- Multi-file patch format
@
-}
module Tool.ASTEdit.Types
  ( -- * Edit Modes
    EditMode(..)
  , editModeFromString
    -- * Common Types
  , Span(..)
  , Position(..)
  , Change(..)
  , FileChange(..)
  , ChangeType(..)
    -- * Results
  , EditResult(..)
  , ValidationResult(..)
  , ValidationError(..)
  , ValidationWarning(..)
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Argonaut (class EncodeJson, encodeJson)

import Aleph.Coeffect.Spec (ASTLanguage(..))

-- ════════════════════════════════════════════════════════════════════════════
-- EDIT MODES
-- ════════════════════════════════════════════════════════════════════════════

{-| Edit mode determines how changes are applied.

@
  Structural lang  -- Parse to AST, transform, render
  Text             -- Exact string replacement
  Patch            -- Multi-file unified patch
@
-}
data EditMode
  = Structural ASTLanguage
  | Text
  | Patch

derive instance eqEditMode :: Eq EditMode
derive instance genericEditMode :: Generic EditMode _

instance showEditMode :: Show EditMode where
  show = genericShow

editModeFromString :: String -> Maybe EditMode
editModeFromString = case _ of
  "structural" -> Just (Structural ASTUnknown "")
  "text" -> Just Text
  "patch" -> Just Patch
  _ -> Nothing

-- ════════════════════════════════════════════════════════════════════════════
-- COMMON TYPES
-- ════════════════════════════════════════════════════════════════════════════

{-| Source span (byte offsets + line/column). -}
type Span =
  { startByte :: Int
  , endByte :: Int
  , startLine :: Int
  , startCol :: Int
  , endLine :: Int
  , endCol :: Int
  }

type Position =
  { line :: Int
  , column :: Int
  }

{-| Single change within a file. -}
type Change =
  { span :: Span
  , oldText :: String
  , newText :: String
  }

{-| Change type for patch mode. -}
data ChangeType
  = Add
  | Update
  | Delete
  | Move String  -- target path

derive instance eqChangeType :: Eq ChangeType
derive instance genericChangeType :: Generic ChangeType _

instance showChangeType :: Show ChangeType where
  show = genericShow

{-| File-level change (for multi-file operations). -}
type FileChange =
  { filePath :: String
  , changeType :: ChangeType
  , oldContent :: String
  , newContent :: String
  , diff :: String
  , additions :: Int
  , deletions :: Int
  }

-- ════════════════════════════════════════════════════════════════════════════
-- RESULTS
-- ════════════════════════════════════════════════════════════════════════════

type EditResult =
  { success :: Boolean
  , mode :: EditMode
  , filesChanged :: Int
  , changes :: Array FileChange
  , validation :: Maybe ValidationResult
  }

type ValidationResult =
  { syntaxValid :: Boolean
  , typesValid :: Maybe Boolean
  , scopesValid :: Boolean
  , warnings :: Array ValidationWarning
  , errors :: Array ValidationError
  }

type ValidationWarning =
  { message :: String
  , span :: Span
  , code :: String
  }

type ValidationError =
  { message :: String
  , span :: Span
  , code :: String
  }
