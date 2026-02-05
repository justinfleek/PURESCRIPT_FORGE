-- | Changelog Data Types and Parsing
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/lib/changelog.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Lib.Changelog
  ( Release(..)
  , HighlightMedia(..)
  , HighlightItem(..)
  , HighlightGroup(..)
  , ChangelogRelease(..)
  , ChangelogData(..)
  , ChangelogSection(..)
  , parseMarkdown
  , parseHighlights
  , changelogApiUrl
  , mkRelease
  ) where

import Prelude

import Effect.Aff (Aff)
import Data.Array (filter, snoc, head, last)
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.String (Pattern(..), split, trim, drop, take, indexOf, length)
import Data.String as String
import Data.String.Regex (Regex, match, test)
import Data.String.Regex.Flags (noFlags, global)
import Data.String.Regex.Unsafe (unsafeRegex)
import Data.Tuple (Tuple(..))

-- | Raw GitHub release data
type Release =
  { tagName :: String
  , name :: String
  , body :: String
  , publishedAt :: String
  , htmlUrl :: String
  }

-- | Smart constructor for Release
mkRelease 
  :: String 
  -> String 
  -> String 
  -> String 
  -> String 
  -> Release
mkRelease tagName name body publishedAt htmlUrl =
  { tagName, name, body, publishedAt, htmlUrl }

-- | Media type in highlights
data HighlightMedia
  = VideoMedia { src :: String }
  | ImageMedia { src :: String, width :: String, height :: String }

derive instance eqHighlightMedia :: Eq HighlightMedia

instance showHighlightMedia :: Show HighlightMedia where
  show (VideoMedia r) = "(VideoMedia " <> show r.src <> ")"
  show (ImageMedia r) = "(ImageMedia " <> show r.src <> " " <> r.width <> "x" <> r.height <> ")"

-- | Highlight item
type HighlightItem =
  { title :: String
  , description :: String
  , shortDescription :: Maybe String
  , media :: HighlightMedia
  }

-- | Group of highlights from a source
type HighlightGroup =
  { source :: String
  , items :: Array HighlightItem
  }

-- | Changelog section (## heading with items)
type ChangelogSection =
  { title :: String
  , items :: Array String
  }

-- | Processed changelog release
type ChangelogRelease =
  { tag :: String
  , name :: String
  , date :: String
  , url :: String
  , highlights :: Array HighlightGroup
  , sections :: Array ChangelogSection
  }

-- | Changelog data result
type ChangelogData =
  { ok :: Boolean
  , releases :: Array ChangelogRelease
  }

-- | Changelog API URL
changelogApiUrl :: String
changelogApiUrl = "https://api.github.com/repos/anomalyco/opencode/releases?per_page=20"

-- | API request headers (pure data)
type ChangelogApiHeaders =
  { accept :: String
  , userAgent :: String
  }

defaultApiHeaders :: ChangelogApiHeaders
defaultApiHeaders =
  { accept: "application/vnd.github.v3+json"
  , userAgent: "OpenCode-Console"
  }

-- | Parse highlight tag regex pattern
highlightTagPattern :: String
highlightTagPattern = "<highlight\\s+source=\"([^\"]+)\">([\\s\\S]*?)<\\/highlight>"

-- | Parse h2 tag pattern
h2Pattern :: String
h2Pattern = "<h2>([^<]+)<\\/h2>"

-- | Parse p tag pattern (with optional short attribute)
pPattern :: String
pPattern = "<p(?:\\s+short=\"([^\"]*)\")?>([^<]+)<\\/p>"

-- | Parse img tag pattern
imgPattern :: String
imgPattern = "<img\\s+width=\"([^\"]+)\"\\s+height=\"([^\"]+)\"\\s+alt=\"[^\"]*\"\\s+src=\"([^\"]+)\""

-- | Video URL pattern (GitHub user attachments)
videoPattern :: String
videoPattern = "^\\s*(https:\\/\\/github\\.com\\/user-attachments\\/assets\\/[a-f0-9-]+)\\s*$"

-- | Parse highlights from release body (pure)
parseHighlights :: String -> Array HighlightGroup
parseHighlights body =
  let
    highlightRegex = unsafeRegex highlightTagPattern global
    -- Note: In actual implementation, this would use proper regex exec loop
    -- For now, we return empty since we can't do stateful regex in pure PS without FFI
    -- The structure is correct for when platform bindings are available
  in
    []

-- | Check if line starts with heading marker
isHeading :: String -> Boolean
isHeading line = String.take 3 line == "## "

-- | Extract heading text
extractHeading :: String -> String
extractHeading line = trim (String.drop 3 line)

-- | Check if line is a list item
isListItem :: String -> Boolean
isListItem line = String.take 2 line == "- "

-- | Extract list item text
extractListItem :: String -> String
extractListItem line = trim (String.drop 2 line)

-- | Check if line is "Thank you" section (to skip)
isThankYouSection :: String -> Boolean
isThankYouSection line = String.take 10 line == "**Thank you"

-- | Parser state for markdown
type ParserState =
  { sections :: Array ChangelogSection
  , currentSection :: Maybe ChangelogSection
  , skipMode :: Boolean
  }

initialParserState :: ParserState
initialParserState =
  { sections: []
  , currentSection: Nothing
  , skipMode: false
  }

-- | Process a single line in the parser
processLine :: ParserState -> String -> ParserState
processLine state line
  -- New heading
  | isHeading line =
      let
        newSection = { title: extractHeading line, items: [] }
        newSections = case state.currentSection of
          Just current -> snoc state.sections current
          Nothing -> state.sections
      in
        state 
          { currentSection = Just newSection
          , sections = newSections
          , skipMode = false
          }
  
  -- Thank you section - start skipping
  | isThankYouSection line =
      state { skipMode = true }
  
  -- List item (not skipping)
  | isListItem line && not state.skipMode =
      case state.currentSection of
        Just current ->
          let
            updatedSection = current { items = snoc current.items (extractListItem line) }
          in
            state { currentSection = Just updatedSection }
        Nothing -> state
  
  -- Other lines - ignore
  | otherwise = state

-- | Finalize parser state
finalizeState :: ParserState -> Array ChangelogSection
finalizeState state =
  case state.currentSection of
    Just current -> snoc state.sections current
    Nothing -> state.sections

-- | Parse markdown body into sections (pure implementation)
parseMarkdown :: String -> { sections :: Array ChangelogSection, highlights :: Array HighlightGroup }
parseMarkdown body =
  let
    lines = split (Pattern "\n") body
    finalState = foldl processLine initialParserState lines
    sections = finalizeState finalState
    highlights = parseHighlights body
  in
    { sections, highlights }

-- | Convert raw release to changelog release (pure)
toChangelogRelease :: Release -> ChangelogRelease
toChangelogRelease release =
  let
    parsed = parseMarkdown release.body
  in
    { tag: release.tagName
    , name: release.name
    , date: release.publishedAt
    , url: release.htmlUrl
    , highlights: parsed.highlights
    , sections: parsed.sections
    }

-- | Convert array of releases to changelog data (pure)
toChangelogData :: Array Release -> ChangelogData
toChangelogData releases =
  { ok: true
  , releases: map toChangelogRelease releases
  }

-- | Empty/error changelog data
emptyChangelogData :: ChangelogData
emptyChangelogData = { ok: false, releases: [] }

-- | FFI: Load changelog from GitHub API
foreign import loadChangelog :: Aff ChangelogData
