{-|
Module      : Aleph.Coeffect.Spec
Description : Resource specification types
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Resource Specifications

Type-level specifications for indexed resources. Each spec
parameterizes a resource constructor.
-}
module Aleph.Coeffect.Spec
  ( SandboxKind(..)
  , ContainerSpec(..)
  , PathSpec(..)
  , GPUSpec(..)
  , SearchBackend(..)
  , ASTLanguage(..)
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ════════════════════════════════════════════════════════════════════════════
-- SANDBOX SPECIFICATION
-- ════════════════════════════════════════════════════════════════════════════

{-| Sandbox isolation kind.

@
  data SandboxKind where
    SandboxNetwork    : SandboxKind  -- Network isolated
    SandboxFilesystem : SandboxKind  -- Filesystem isolated
    SandboxGPU        : SandboxKind  -- GPU passthrough
    SandboxFull       : SandboxKind  -- Complete isolation
@
-}
data SandboxKind
  = SandboxNetwork
  | SandboxFilesystem
  | SandboxGPU
  | SandboxFull

derive instance eqSandboxKind :: Eq SandboxKind
derive instance ordSandboxKind :: Ord SandboxKind
derive instance genericSandboxKind :: Generic SandboxKind _

instance showSandboxKind :: Show SandboxKind where
  show = genericShow

-- ════════════════════════════════════════════════════════════════════════════
-- CONTAINER SPECIFICATION
-- ════════════════════════════════════════════════════════════════════════════

{-| Container specification for gVisor. -}
type ContainerSpec =
  { image :: String
  , memoryMB :: Int
  , cpuPercent :: Int
  , timeoutMs :: Int
  , networkIsolated :: Boolean
  , filesystemReadOnly :: Boolean
  }

-- ════════════════════════════════════════════════════════════════════════════
-- FILESYSTEM SPECIFICATION
-- ════════════════════════════════════════════════════════════════════════════

{-| Filesystem path specification. -}
type PathSpec =
  { path :: String
  , readable :: Boolean
  , writable :: Boolean
  , recursive :: Boolean
  }

-- ════════════════════════════════════════════════════════════════════════════
-- GPU SPECIFICATION
-- ════════════════════════════════════════════════════════════════════════════

{-| GPU compute specification. -}
type GPUSpec =
  { deviceIndex :: Maybe Int
  , memoryMB :: Maybe Int
  , computeCapability :: Maybe String
  }

-- ════════════════════════════════════════════════════════════════════════════
-- SEARCH BACKEND SPECIFICATION
-- ════════════════════════════════════════════════════════════════════════════

{-| Search backend specification.

@
  data SearchBackend where
    SearXNG      : String → SearchBackend  -- Instance URL
    BraveSearch  : SearchBackend
    CustomSearch : String → SearchBackend
@
-}
data SearchBackend
  = SearXNG String
  | BraveSearch
  | CustomSearch String

derive instance eqSearchBackend :: Eq SearchBackend
derive instance ordSearchBackend :: Ord SearchBackend
derive instance genericSearchBackend :: Generic SearchBackend _

instance showSearchBackend :: Show SearchBackend where
  show = genericShow

-- ════════════════════════════════════════════════════════════════════════════
-- AST LANGUAGE SPECIFICATION
-- ════════════════════════════════════════════════════════════════════════════

{-| AST language specification.

@
  data ASTLanguage where
    ASTPureScript : ASTLanguage
    ASTHaskell    : ASTLanguage
    ASTLean4      : ASTLanguage
    ASTTypeScript : ASTLanguage
    ASTNix        : ASTLanguage
    ASTPython     : ASTLanguage
    ASTRust       : ASTLanguage
    ASTUnknown    : String → ASTLanguage
@
-}
data ASTLanguage
  = ASTPureScript
  | ASTHaskell
  | ASTLean4
  | ASTTypeScript
  | ASTNix
  | ASTPython
  | ASTRust
  | ASTUnknown String

derive instance eqASTLanguage :: Eq ASTLanguage
derive instance ordASTLanguage :: Ord ASTLanguage
derive instance genericASTLanguage :: Generic ASTLanguage _

instance showASTLanguage :: Show ASTLanguage where
  show = genericShow
