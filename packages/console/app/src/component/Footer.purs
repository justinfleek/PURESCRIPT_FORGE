-- | Footer Component
-- |
-- | Site footer with navigation links.
-- | Pure data representation of footer structure.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/component/footer.tsx
module Forge.Console.App.Component.Footer
  ( FooterLink(..)
  , getFooterLinks
  , formatStarCount
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- | Footer link types
data FooterLink
  = GitHubLink { url :: String, starCount :: String }
  | DocsLink
  | ChangelogLink
  | DiscordLink
  | TwitterLink { url :: String }

derive instance eqFooterLink :: Eq FooterLink

instance showFooterLink :: Show FooterLink where
  show (GitHubLink r) = "GitHub [" <> r.starCount <> "]"
  show DocsLink = "Docs"
  show ChangelogLink = "Changelog"
  show DiscordLink = "Discord"
  show (TwitterLink _) = "X"

-- | Get footer links with configuration
getFooterLinks :: { githubUrl :: String, twitterUrl :: String } -> Int -> Array FooterLink
getFooterLinks config stars =
  [ GitHubLink { url: config.githubUrl, starCount: formatStarCount stars }
  , DocsLink
  , ChangelogLink
  , DiscordLink
  , TwitterLink { url: config.twitterUrl }
  ]

-- | Format star count with compact notation
formatStarCount :: Int -> String
formatStarCount stars
  | stars >= 1000000 = show (stars / 1000000) <> "M"
  | stars >= 1000 = show (stars / 1000) <> "K"
  | otherwise = show stars
