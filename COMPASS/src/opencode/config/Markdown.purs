-- | Markdown config parsing
module Opencode.Config.Markdown where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.String as String
import Data.Array as Array

-- | Parse markdown config file
parseMarkdownConfig :: String -> Aff (Either String String)
parseMarkdownConfig content = do
  -- Extract frontmatter and return it
  let frontmatter = extractFrontmatter content
  if String.null frontmatter
    then pure $ Left "No frontmatter found"
    else pure $ Right frontmatter

-- | Extract frontmatter from markdown
-- | Extracts YAML frontmatter between --- delimiters
extractFrontmatter :: String -> String
extractFrontmatter content =
  let lines = String.split (String.Pattern "\n") content
  in case Array.head lines of
    Just firstLine | String.trim firstLine == "---" ->
      -- Find the closing ---
      let restLines = Array.drop 1 lines
          frontmatterLines = Array.takeWhile (\line -> String.trim line /= "---") restLines
      in String.joinWith "\n" frontmatterLines
    _ -> ""
