-- | Markdown config parsing
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/config/markdown.ts
module Opencode.Config.Markdown where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Parse markdown config file
parseMarkdownConfig :: String -> Aff (Either String String)
parseMarkdownConfig content = notImplemented "Config.Markdown.parseMarkdownConfig"

-- | Extract frontmatter from markdown
extractFrontmatter :: String -> String
extractFrontmatter content = "" -- TODO: Implement
