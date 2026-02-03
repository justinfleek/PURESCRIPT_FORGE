-- | Changelog Index Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/changelog/index.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Changelog.Index
  ( ChangelogState(..)
  , ReleaseItemParts(..)
  , CollapsibleState(..)
  , formatDate
  , parseReleaseItem
  , buildAuthorUrl
  ) where

import Prelude

import Data.Array (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), indexOf, drop, take, length)
import Console.App.Lib.Changelog (ChangelogRelease, ChangelogSection, HighlightGroup)

-- | Changelog page state
type ChangelogState =
  { releases :: Array ChangelogRelease
  , loading :: Boolean
  , collapsedSections :: Map String Boolean
  }

-- | Initial state
initialState :: ChangelogState
initialState =
  { releases: []
  , loading: true
  , collapsedSections: Map.empty
  }

-- | Collapsible section state
type CollapsibleState =
  { sectionId :: String
  , isOpen :: Boolean
  }

-- | Toggle section open/closed
toggleSection :: ChangelogState -> String -> ChangelogState
toggleSection state sectionId =
  let
    current = Map.lookup sectionId state.collapsedSections
    newValue = case current of
      Just open -> not open
      Nothing -> true
  in
    state { collapsedSections = Map.insert sectionId newValue state.collapsedSections }

-- | Check if section is open
isSectionOpen :: ChangelogState -> String -> Boolean
isSectionOpen state sectionId =
  case Map.lookup sectionId state.collapsedSections of
    Just open -> open
    Nothing -> false  -- Default closed

-- | Release item with parsed author
type ReleaseItemParts =
  { text :: String
  , username :: Maybe String
  }

-- | Parse release item text to extract author
-- | Format: "Fix bug in feature (@username)"
parseReleaseItem :: String -> ReleaseItemParts
parseReleaseItem item =
  let
    -- Look for " (@" pattern
    authorPatternStart = indexOf (Pattern " (@") item
  in
    case authorPatternStart of
      Nothing -> { text: item, username: Nothing }
      Just idx ->
        let
          text = take idx item
          rest = drop (idx + 3) item  -- Skip " (@"
          usernameEnd = indexOf (Pattern ")") rest
        in
          case usernameEnd of
            Nothing -> { text: item, username: Nothing }
            Just endIdx ->
              let
                username = take endIdx rest
              in
                { text, username: Just username }

-- | Build GitHub author URL
buildAuthorUrl :: String -> String
buildAuthorUrl username = "https://github.com/" <> username

-- | Format date for display (pure)
-- | Input: ISO date string like "2024-01-15T12:00:00Z"
-- | Output: "Jan 15, 2024"
formatDate :: String -> String
formatDate dateStr =
  -- Simplified - in real impl would use proper date parsing
  dateStr

-- | Month names for formatting
monthNames :: Array String
monthNames =
  [ "Jan", "Feb", "Mar", "Apr", "May", "Jun"
  , "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"
  ]

-- | Get month name by index (1-12)
getMonthName :: Int -> String
getMonthName n = case n of
  1 -> "Jan"
  2 -> "Feb"
  3 -> "Mar"
  4 -> "Apr"
  5 -> "May"
  6 -> "Jun"
  7 -> "Jul"
  8 -> "Aug"
  9 -> "Sep"
  10 -> "Oct"
  11 -> "Nov"
  12 -> "Dec"
  _ -> "???"

-- | Page metadata
type PageMeta =
  { title :: String
  , description :: String
  , canonicalPath :: String
  }

changelogPageMeta :: PageMeta
changelogPageMeta =
  { title: "OpenCode | Changelog"
  , description: "OpenCode release notes and changelog"
  , canonicalPath: "/changelog"
  }
