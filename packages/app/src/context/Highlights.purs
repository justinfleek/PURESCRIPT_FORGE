-- | Highlights context - manages release notes highlights
-- | Migrated from: forge-dev/packages/app/src/context/highlights.tsx
module App.Context.Highlights
  ( Highlight
  , HighlightMedia
  , ParsedRelease
  , HighlightsStore
  , mkHighlightsStore
  , normalizeVersion
  , parseHighlight
  , sliceHighlights
  , markSeen
  ) where

import Prelude

import Data.Array (filter, findIndex, length, slice, take, (:))
import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.String (drop, trim, toLower)
import Data.String as String

-- | Highlight media (image or video)
type HighlightMedia =
  { mediaType :: String  -- "image" | "video"
  , src :: String
  , alt :: String
  }

-- | Release highlight
type Highlight =
  { title :: String
  , description :: String
  , media :: Maybe HighlightMedia
  }

-- | Parsed release from changelog
type ParsedRelease =
  { tag :: Maybe String
  , highlights :: Array Highlight
  }

-- | Highlights store state
type HighlightsStore =
  { version :: Maybe String
  }

-- | Create initial highlights store
mkHighlightsStore :: HighlightsStore
mkHighlightsStore = { version: Nothing }

-- | Normalize version string (strip leading v/V)
normalizeVersion :: Maybe String -> Maybe String
normalizeVersion Nothing = Nothing
normalizeVersion (Just v) =
  let
    text = trim v
  in
    if text == ""
    then Nothing
    else
      let
        first = String.take 1 text
      in
        if first == "v" || first == "V"
        then Just (drop 1 text)
        else Just text

-- | Parse a highlight from JSON-like record
parseHighlight :: { title :: Maybe String, description :: Maybe String, media :: Maybe { mediaType :: Maybe String, src :: Maybe String } } -> Maybe Highlight
parseHighlight input =
  case input.title of
    Nothing -> Nothing
    Just title ->
      case input.description of
        Nothing -> Nothing
        Just description ->
          let
            media = case input.media of
              Nothing -> Nothing
              Just m ->
                case m.mediaType, m.src of
                  Just mt, Just src ->
                    let
                      mType = toLower mt
                    in
                      if mType == "image" || mType == "video"
                      then Just { mediaType: mType, src, alt: title }
                      else Nothing
                  _, _ -> Nothing
          in
            Just { title, description, media }

-- | Slice highlights from releases between versions
sliceHighlights :: { releases :: Array ParsedRelease, current :: Maybe String, previous :: Maybe String } -> Array Highlight
sliceHighlights input =
  let
    current = normalizeVersion input.current
    previous = normalizeVersion input.previous
    releases = input.releases
    
    -- Find start index (current version or 0)
    startIdx = case current of
      Nothing -> 0
      Just c ->
        case findIndex (\r -> normalizeVersion r.tag == Just c) releases of
          Nothing -> 0
          Just i -> i
    
    -- Find end index (previous version or end)
    endIdx = case previous of
      Nothing -> length releases
      Just p ->
        case findIndex (\r -> i >= startIdx && normalizeVersion r.tag == Just p) (withIndex releases) of
          Nothing -> length releases
          Just i -> i
    
    -- Slice releases
    sliced = slice startIdx endIdx releases
    
    -- Flatten highlights
    allHighlights = Array.concatMap _.highlights sliced
    
    -- Deduplicate
    unique = dedupe allHighlights
  in
    take 5 unique
  where
    -- Helper to get indexed elements
    withIndex :: forall a. Array a -> Array { i :: Int, r :: a }
    withIndex arr = Array.mapWithIndex (\i r -> { i, r }) arr
    
    i :: forall r. { i :: Int | r } -> Int
    i = _.i
    
    -- Deduplicate highlights by content
    dedupe :: Array Highlight -> Array Highlight
    dedupe highlights =
      let
        go acc seen [] = acc
        go acc seen (h : rest) =
          let
            key = h.title <> "\n" <> h.description <> "\n" <> 
                  fromMaybe "" (map _.mediaType h.media) <> "\n" <>
                  fromMaybe "" (map _.src h.media)
          in
            if Set.member key seen
            then go acc seen rest
            else go (Array.snoc acc h) (Set.insert key seen) rest
      in
        go [] Set.empty highlights

-- | Mark a version as seen
markSeen :: String -> HighlightsStore -> HighlightsStore
markSeen version store = store { version = Just version }
