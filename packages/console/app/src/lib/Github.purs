-- | GitHub API Data Types
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/lib/github.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Lib.Github
  ( GithubMeta(..)
  , GithubRelease(..)
  , GithubData(..)
  , ContributorCount
  , StarCount
  , mkContributorCount
  , mkStarCount
  , githubApiUrl
  , releasesApiUrl
  , contributorsApiUrl
  , parseContributorCount
  , buildGithubData
  ) where

import Prelude

import Data.Array (head) as Array
import Data.Either (Either(..))
import Data.Int (fromString)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), split, indexOf, drop, take)
import Data.String as String
import Data.String.Regex (Regex, match)
import Data.String.Regex.Flags (noFlags)
import Data.String.Regex.Unsafe (unsafeRegex)

-- | Star count (non-negative integer)
newtype StarCount = StarCount Int

derive instance eqStarCount :: Eq StarCount
derive instance ordStarCount :: Ord StarCount

instance showStarCount :: Show StarCount where
  show (StarCount n) = show n

-- | Smart constructor for star count
mkStarCount :: Int -> Maybe StarCount
mkStarCount n
  | n >= 0 = Just (StarCount n)
  | otherwise = Nothing

-- | Contributor count (non-negative integer)
newtype ContributorCount = ContributorCount Int

derive instance eqContributorCount :: Eq ContributorCount
derive instance ordContributorCount :: Ord ContributorCount

instance showContributorCount :: Show ContributorCount where
  show (ContributorCount n) = show n

-- | Smart constructor for contributor count
mkContributorCount :: Int -> Maybe ContributorCount
mkContributorCount n
  | n >= 0 = Just (ContributorCount n)
  | otherwise = Nothing

-- | GitHub release info
type GithubRelease =
  { name :: String
  , url :: String
  , tagName :: String
  }

-- | GitHub repository metadata
type GithubMeta =
  { stargazersCount :: Int
  }

-- | Combined GitHub data
type GithubData =
  { stars :: StarCount
  , release :: GithubRelease
  , contributors :: ContributorCount
  }

-- | Repository URL configuration
type RepoConfig =
  { owner :: String
  , repo :: String
  }

-- | Default repo config (opencode)
defaultRepoConfig :: RepoConfig
defaultRepoConfig =
  { owner: "anomalyco"
  , repo: "opencode"
  }

-- | Build GitHub API base URL from repo URL
githubApiUrl :: String -> String
githubApiUrl repoUrl =
  -- Convert https://github.com/owner/repo to https://api.github.com/repos/owner/repo
  let
    prefix = "https://github.com/"
    apiPrefix = "https://api.github.com/repos/"
  in
    if String.take (String.length prefix) repoUrl == prefix then
      apiPrefix <> String.drop (String.length prefix) repoUrl
    else
      repoUrl

-- | Releases API URL
releasesApiUrl :: String -> String
releasesApiUrl baseUrl = baseUrl <> "/releases"

-- | Contributors API URL (with per_page=1 for pagination header)
contributorsApiUrl :: String -> String
contributorsApiUrl baseUrl = baseUrl <> "/contributors?per_page=1"

-- | User agent header for GitHub API
userAgentHeader :: String
userAgentHeader = "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/108.0.0.0 Safari/537.36"

-- | API request headers (pure data)
type GithubApiHeaders =
  { userAgent :: String
  }

defaultApiHeaders :: GithubApiHeaders
defaultApiHeaders =
  { userAgent: userAgentHeader
  }

-- | Parse contributor count from Link header
-- | Link header format: <url>; rel="next", <url?page=N>; rel="last"
-- | We extract N from the "last" link
parseContributorCount :: Maybe String -> ContributorCount
parseContributorCount linkHeaderM = case linkHeaderM of
  Nothing -> ContributorCount 0
  Just linkHeader ->
    let
      -- Pattern to match &page=N>; rel="last"
      pagePattern = unsafeRegex "&page=(\\d+)>; rel=\"last\"" noFlags
      matched = match pagePattern linkHeader
    in
      case matched of
        Just matches ->
          case matches of
            [_, Just numStr] ->
              case fromString numStr of
                Just n -> ContributorCount n
                Nothing -> ContributorCount 0
            _ -> ContributorCount 0
        Nothing -> ContributorCount 0

-- | Build GitHub data from API responses (pure)
buildGithubData 
  :: { stargazersCount :: Int }  -- repo meta
  -> Array { name :: String, htmlUrl :: String, tagName :: String }  -- releases
  -> Maybe String  -- Link header from contributors request
  -> Maybe GithubData
buildGithubData meta releases linkHeader = do
  -- Need at least one release
  release <- Array.head releases
  
  stars <- mkStarCount meta.stargazersCount
  
  let contributors = parseContributorCount linkHeader
  
  pure
    { stars
    , release:
        { name: release.name
        , url: release.htmlUrl
        , tagName: release.tagName
        }
    , contributors
    }

-- | Format star count for display
formatStarCount :: StarCount -> String
formatStarCount (StarCount n)
  | n >= 1000 = show (n / 1000) <> "k"
  | otherwise = show n

-- | Format contributor count for display
formatContributorCount :: ContributorCount -> String
formatContributorCount (ContributorCount n) = show n
