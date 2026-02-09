{-|
Module      : Forge.Config.Markdown
Description : Markdown Configuration Parsing

Parses markdown files with YAML frontmatter for configuration.
Used for skills, prompts, and other markdown-based configurations.

== Format

@
---
name: my-config
description: A configuration file
tags:
  - tag1
  - tag2
---

# Content

The markdown content goes here...
@
-}
module Forge.Config.Markdown
  ( -- * Types
    MarkdownConfig
  , Frontmatter
    -- * Parsing
  , parseMarkdownConfig
  , extractFrontmatter
  , extractContent
    -- * Utilities
  , hasFrontmatter
  , getFrontmatterValue
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Frontmatter key-value pairs
type Frontmatter =
  { name :: Maybe String
  , description :: Maybe String
  , tags :: Array String
  , raw :: String  -- Raw YAML content
  }

-- | Parsed markdown configuration
type MarkdownConfig =
  { frontmatter :: Maybe Frontmatter
  , content :: String
  , rawContent :: String
  }

-- ============================================================================
-- PARSING
-- ============================================================================

{-| Parse a markdown configuration file.

Extracts YAML frontmatter (if present) and markdown content.
-}
parseMarkdownConfig :: String -> Aff (Either String MarkdownConfig)
parseMarkdownConfig content = do
  let trimmed = String.trim content
  
  -- Check for frontmatter
  if hasFrontmatter trimmed
    then do
      let fm = extractFrontmatter trimmed
      let body = extractContent trimmed
      pure $ Right
        { frontmatter: Just (parseFrontmatter fm)
        , content: body
        , rawContent: content
        }
    else
      pure $ Right
        { frontmatter: Nothing
        , content: trimmed
        , rawContent: content
        }

{-| Extract frontmatter from markdown content.

Returns the YAML content between the --- delimiters.
-}
extractFrontmatter :: String -> String
extractFrontmatter content =
  if not (hasFrontmatter content)
    then ""
    else
      let lines = String.split (String.Pattern "\n") content
          -- Drop first "---"
          afterFirst = Array.drop 1 lines
          -- Take until second "---"
          fmLines = Array.takeWhile (_ /= "---") afterFirst
      in String.joinWith "\n" fmLines

{-| Extract markdown content (after frontmatter). -}
extractContent :: String -> String
extractContent content =
  if not (hasFrontmatter content)
    then content
    else
      let lines = String.split (String.Pattern "\n") content
          -- Drop first "---"
          afterFirst = Array.drop 1 lines
          -- Drop frontmatter lines and second "---"
          afterFrontmatter = Array.dropWhile (_ /= "---") afterFirst
          -- Drop the second "---"
          body = Array.drop 1 afterFrontmatter
      in String.trim $ String.joinWith "\n" body

-- ============================================================================
-- UTILITIES
-- ============================================================================

{-| Check if content has YAML frontmatter. -}
hasFrontmatter :: String -> Boolean
hasFrontmatter content =
  startsWith "---" (String.trim content)
  where
    startsWith prefix str = String.take (String.length prefix) str == prefix

{-| Get a value from frontmatter by key.

Simple key: value parsing. Does not handle complex YAML.
-}
getFrontmatterValue :: String -> String -> Maybe String
getFrontmatterValue key frontmatter =
  let lines = String.split (String.Pattern "\n") frontmatter
      matchingLine = Array.find (isKeyLine key) lines
  in matchingLine >>= extractValue
  where
    isKeyLine :: String -> String -> Boolean
    isKeyLine k line = 
      let prefix = k <> ":"
          trimmed = String.trim line
      in String.take (String.length prefix) trimmed == prefix
    
    extractValue :: String -> Maybe String
    extractValue line =
      let parts = String.split (String.Pattern ":") line
      in case Array.drop 1 parts of
        [] -> Nothing
        rest -> Just $ String.trim $ String.joinWith ":" rest

-- ============================================================================
-- HELPERS
-- ============================================================================

parseFrontmatter :: String -> Frontmatter
parseFrontmatter raw =
  { name: getFrontmatterValue "name" raw
  , description: getFrontmatterValue "description" raw
  , tags: parseTags raw
  , raw
  }

parseTags :: String -> Array String
parseTags content =
  let lines = String.split (String.Pattern "\n") content
      tagLines = Array.filter isTagLine lines
  in Array.mapMaybe extractTag tagLines
  where
    isTagLine line = 
      let trimmed = String.trim line
      in startsWith "- " trimmed || startsWith "tags:" trimmed
    
    extractTag line =
      let trimmed = String.trim line
      in if startsWith "- " trimmed
         then Just $ String.trim $ String.drop 2 trimmed
         else Nothing
    
    startsWith prefix str = String.take (String.length prefix) str == prefix
