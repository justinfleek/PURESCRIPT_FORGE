{-|
Module      : Tool.Search.Engines
Description : Search engine definitions
= Search Engines

Defines all supported search engines and their mappings to SearXNG
engine identifiers.

== Engine Categories

| Category  | Engines                                              |
|-----------|------------------------------------------------------|
| Web       | google, bing, duckduckgo, brave, qwant, startpage   |
| Images    | google images, bing images, flickr, unsplash        |
| Videos    | youtube, vimeo, dailymotion, peertube               |
| News      | google news, bing news, wikinews                    |
| Science   | arxiv, google scholar, semantic scholar, pubmed     |
| Code      | github, gitlab, codeberg, sourcegraph               |
| Files     | fdroid, npm, pypi, crates, hackage                  |
-}
module Tool.Search.Engines
  ( -- * Engine Type
    Engine(..)
  , engineToString
    -- * Category Type
  , Category(..)
  , categoryToString
  , enginesForCategory
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Argonaut (class EncodeJson, encodeJson)

-- ============================================================================
-- ENGINES
-- ============================================================================

{-| Search engine identifiers.

Each constructor maps to a SearXNG engine name via `engineToString`.
-}
data Engine
  -- Web
  = Google
  | Bing
  | DuckDuckGo
  | Brave
  | Qwant
  | StartPage
  | Mojeek
  | Wikipedia
  | Wikidata
  -- Code
  | GitHub
  | GitLab
  | Codeberg
  | SourceGraph
  | StackOverflow
  | HackerNews
  -- Science
  | Arxiv
  | GoogleScholar
  | SemanticScholar
  | PubMed
  | Crossref
  | OpenAlex
  | DBLP
  -- Images
  | GoogleImages
  | BingImages
  | Flickr
  | Unsplash
  | WikimediaCommons
  -- Video
  | YouTube
  | Vimeo
  | PeerTube
  | Dailymotion
  -- News
  | GoogleNews
  | BingNews
  | WikiNews
  -- Files/Packages
  | FDroid
  | NPM
  | PyPI
  | Crates
  | Hackage

derive instance eqEngine :: Eq Engine
derive instance ordEngine :: Ord Engine
derive instance genericEngine :: Generic Engine _

instance showEngine :: Show Engine where
  show = genericShow

instance encodeJsonEngine :: EncodeJson Engine where
  encodeJson = encodeJson <<< engineToString

-- | Convert engine to SearXNG identifier
engineToString :: Engine -> String
engineToString = case _ of
  Google -> "google"
  Bing -> "bing"
  DuckDuckGo -> "duckduckgo"
  Brave -> "brave"
  Qwant -> "qwant"
  StartPage -> "startpage"
  Mojeek -> "mojeek"
  Wikipedia -> "wikipedia"
  Wikidata -> "wikidata"
  GitHub -> "github"
  GitLab -> "gitlab"
  Codeberg -> "codeberg"
  SourceGraph -> "sourcegraph"
  StackOverflow -> "stackoverflow"
  HackerNews -> "hackernews"
  Arxiv -> "arxiv"
  GoogleScholar -> "google scholar"
  SemanticScholar -> "semantic scholar"
  PubMed -> "pubmed"
  Crossref -> "crossref"
  OpenAlex -> "openalex"
  DBLP -> "dblp"
  GoogleImages -> "google images"
  BingImages -> "bing images"
  Flickr -> "flickr"
  Unsplash -> "unsplash"
  WikimediaCommons -> "wikimedia commons"
  YouTube -> "youtube"
  Vimeo -> "vimeo"
  PeerTube -> "peertube"
  Dailymotion -> "dailymotion"
  GoogleNews -> "google news"
  BingNews -> "bing news"
  WikiNews -> "wikinews"
  FDroid -> "fdroid"
  NPM -> "npm"
  PyPI -> "pypi"
  Crates -> "crates.io"
  Hackage -> "hackage"

-- ============================================================================
-- CATEGORIES
-- ============================================================================

{-| Search categories supported by SearXNG. -}
data Category
  = General
  | Images
  | Videos
  | News
  | Science
  | IT
  | Files
  | Music
  | SocialMedia

derive instance eqCategory :: Eq Category
derive instance ordCategory :: Ord Category
derive instance genericCategory :: Generic Category _

instance showCategory :: Show Category where
  show = genericShow

instance encodeJsonCategory :: EncodeJson Category where
  encodeJson = encodeJson <<< categoryToString

-- | Convert category to SearXNG identifier
categoryToString :: Category -> String
categoryToString = case _ of
  General -> "general"
  Images -> "images"
  Videos -> "videos"
  News -> "news"
  Science -> "science"
  IT -> "it"
  Files -> "files"
  Music -> "music"
  SocialMedia -> "social media"

-- | Get default engines for a category
enginesForCategory :: Category -> Array Engine
enginesForCategory = case _ of
  General -> [Google, Bing, DuckDuckGo, Brave, Wikipedia]
  Images -> [GoogleImages, BingImages, Flickr, Unsplash]
  Videos -> [YouTube, Vimeo, PeerTube]
  News -> [GoogleNews, BingNews, WikiNews]
  Science -> [Arxiv, GoogleScholar, SemanticScholar, PubMed, DBLP]
  IT -> [GitHub, GitLab, StackOverflow, SourceGraph, HackerNews]
  Files -> [FDroid, NPM, PyPI, Crates, Hackage]
  Music -> []  -- Add music engines as needed
  SocialMedia -> [HackerNews]
