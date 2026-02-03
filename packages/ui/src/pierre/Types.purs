-- | Pierre Diff Viewer Types
-- |
-- | Type definitions for the Pierre diff viewer component.
-- | Provides type-safe representations of diff options, file contents,
-- | and line annotations.
-- |
-- | Source: _OTHER/opencode-original/packages/ui/src/pierre/index.ts
module Forge.UI.Pierre.Types
  ( DiffProps
  , FileContents
  , DiffLineAnnotation
  , SelectedLineRange
  , FileDiffOptions
  , DiffStyle(..)
  , LineDiffType(..)
  , DiffIndicators(..)
  , Overflow(..)
  , ThemeType(..)
  , WorkerPoolStyle(..)
  ) where

import Prelude

import Data.Maybe (Maybe)
import Foreign.Object (Object)

-- | Diff display style
data DiffStyle
  = Unified
  | Split

derive instance eqDiffStyle :: Eq DiffStyle

instance showDiffStyle :: Show DiffStyle where
  show Unified = "unified"
  show Split = "split"

-- | Line diff algorithm type
data LineDiffType
  = LineDiffNone
  | LineDiffWordAlt

derive instance eqLineDiffType :: Eq LineDiffType

instance showLineDiffType :: Show LineDiffType where
  show LineDiffNone = "none"
  show LineDiffWordAlt = "word-alt"

-- | Diff indicator style
data DiffIndicators
  = Bars
  | Signs

derive instance eqDiffIndicators :: Eq DiffIndicators

instance showDiffIndicators :: Show DiffIndicators where
  show Bars = "bars"
  show Signs = "signs"

-- | Text overflow handling
data Overflow
  = Wrap
  | Scroll

derive instance eqOverflow :: Eq Overflow

instance showOverflow :: Show Overflow where
  show Wrap = "wrap"
  show Scroll = "scroll"

-- | Theme type for diff display
data ThemeType
  = System
  | Light
  | Dark

derive instance eqThemeType :: Eq ThemeType

instance showThemeType :: Show ThemeType where
  show System = "system"
  show Light = "light"
  show Dark = "dark"

-- | Worker pool style
data WorkerPoolStyle
  = UnifiedPool
  | SplitPool

derive instance eqWorkerPoolStyle :: Eq WorkerPoolStyle

instance showWorkerPoolStyle :: Show WorkerPoolStyle where
  show UnifiedPool = "unified"
  show SplitPool = "split"

-- | File contents for diff comparison
-- | Represents the content of a file with optional path and language
type FileContents =
  { content :: String
  , path :: Maybe String
  , language :: Maybe String
  }

-- | Selected line range for highlighting
type SelectedLineRange =
  { start :: Int
  , end :: Int
  , side :: Maybe String  -- "before" | "after" | Nothing for unified
  }

-- | Line annotation for adding metadata to diff lines
type DiffLineAnnotation r =
  { line :: Int
  , side :: String  -- "before" | "after"
  | r
  }

-- | File diff display options
-- | Configuration for how diffs are rendered
type FileDiffOptions r =
  { theme :: String
  , themeType :: ThemeType
  , disableLineNumbers :: Boolean
  , overflow :: Overflow
  , diffStyle :: DiffStyle
  , diffIndicators :: DiffIndicators
  , disableBackground :: Boolean
  , expansionLineCount :: Int
  , lineDiffType :: LineDiffType
  , maxLineDiffLength :: Int
  , maxLineLengthForHighlighting :: Int
  , disableFileHeader :: Boolean
  , unsafeCSS :: String
  | r
  }

-- | Props for the diff component
-- | Combines file contents with display options
type DiffProps r =
  { before :: FileContents
  , after :: FileContents
  , annotations :: Maybe (Array (DiffLineAnnotation ()))
  , selectedLines :: Maybe SelectedLineRange
  , commentedLines :: Maybe (Array SelectedLineRange)
  , onRendered :: Maybe (Unit -> Unit)
  , class :: Maybe String
  , classList :: Maybe (Object Boolean)
  | r
  }
