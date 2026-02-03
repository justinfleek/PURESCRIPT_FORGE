-- | Marked Context - Markdown Parser with Syntax Highlighting
-- |
-- | Provides a markdown parser with:
-- | - KaTeX math rendering (inline $ and display $$)
-- | - Shiki syntax highlighting for code blocks
-- | - Custom Forge theme for syntax colors
-- |
-- | Source: _OTHER/opencode-original/packages/ui/src/context/marked.tsx
module Forge.UI.Context.Marked
  ( MarkedContext
  , MarkedProvider
  , useMarked
  , NativeMarkdownParser
  , parseMarkdown
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref

-- | Native markdown parser function type
type NativeMarkdownParser = String -> Aff String

-- | Marked context interface
type MarkedContext =
  { parse :: String -> Aff String
  }

-- | Internal context reference
foreign import markedContextRef :: Ref (Maybe MarkedContext)

-- | Provider props
type MarkedProviderProps =
  { nativeParser :: Maybe NativeMarkdownParser
  }

-- | Marked provider component type
type MarkedProvider = MarkedProviderProps -> Effect MarkedContext

-- | Parse markdown using the marked library with extensions
foreign import parseMarkdownImpl :: String -> Aff String

-- | Render math expressions in text (KaTeX)
foreign import renderMathExpressions :: String -> String

-- | Highlight code blocks using Shiki
foreign import highlightCodeBlocks :: String -> Aff String

-- | Parse markdown with full processing pipeline
parseMarkdown :: Maybe NativeMarkdownParser -> String -> Aff String
parseMarkdown mNativeParser markdown = do
  case mNativeParser of
    Just nativeParser -> do
      html <- nativeParser markdown
      let withMath = renderMathExpressions html
      highlightCodeBlocks withMath
    Nothing ->
      parseMarkdownImpl markdown

-- | Use the marked context
useMarked :: Effect MarkedContext
useMarked = do
  mCtx <- Ref.read markedContextRef
  case mCtx of
    Nothing -> throw "Marked context must be used within a MarkedProvider"
    Just ctx -> pure ctx

-- | Initialize marked context
initMarkedContext :: Maybe NativeMarkdownParser -> Effect MarkedContext
initMarkedContext mNativeParser = do
  pure
    { parse: parseMarkdown mNativeParser
    }
