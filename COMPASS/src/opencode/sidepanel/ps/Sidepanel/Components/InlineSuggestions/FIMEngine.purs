{-|
Module      : Sidepanel.Components.InlineSuggestions.FIMEngine
Description : Fill-in-the-Middle (FIM) code completion engine
FIM (Fill-in-the-Middle) is a powerful code completion technique where the model
predicts code that goes in the middle of existing code, not just at the end.

This enables:
- Completing function bodies when signature exists
- Filling in missing implementations
- Completing between existing code blocks
- More context-aware suggestions
-}
module Sidepanel.Components.InlineSuggestions.FIMEngine where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)
import Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes
  ( EditorState
  , InlineSuggestion
  , Position
  , Range
  , CompletionKind(..)
  )
import Sidepanel.Components.InlineSuggestions.ProviderIntegration
  ( ProviderIntegrationState
  , generateFIMWithProvider
  )

-- | FIM request with prefix and suffix
type FIMRequest =
  { prefix :: String  -- Code before insertion point
  , suffix :: String  -- Code after insertion point
  , language :: String
  , maxTokens :: Int
  , temperature :: Number
  }

-- | FIM response
type FIMResponse =
  { completion :: String
  , confidence :: Number
  , alternatives :: Array String
  }

-- | Generate FIM completion using ProviderIntegration
generateFIMCompletion :: Maybe ProviderIntegrationState -> FIMRequest -> Position -> Aff FIMResponse
generateFIMCompletion providerStateM request position = do
  case providerStateM of
    Nothing -> pure
      { completion: ""
      , confidence: 0.0
      , alternatives: []
      }
    Just providerState -> do
      -- Call ProviderIntegration for FIM completion
      suggestion <- generateFIMWithProvider providerState
        { prefix: request.prefix
        , suffix: request.suffix
        , language: request.language
        }
        position
      
      -- Convert suggestion to FIM response
      pure
        { completion: suggestion.text
        , confidence: suggestion.confidence
        , alternatives: suggestion.alternatives
        }

-- | Extract FIM context from editor state
extractFIMContext :: EditorState -> FIMRequest
extractFIMContext editorState = do
  let lines = String.split (String.Pattern "\n") editorState.content
  let cursorLine = editorState.cursorPosition.line
  let cursorCol = editorState.cursorPosition.column
  
  -- Extract prefix (everything before cursor)
  let prefixLines = Array.take cursorLine lines
  let currentLinePrefix = case Array.index lines cursorLine of
    Nothing -> ""
    Just line -> String.take cursorCol line
  let prefix = String.joinWith "\n" prefixLines <> "\n" <> currentLinePrefix
  
  -- Extract suffix (everything after cursor)
  let currentLineSuffix = case Array.index lines cursorLine of
    Nothing -> ""
    Just line -> String.drop cursorCol line
  let suffixLines = Array.drop (cursorLine + 1) lines
  let suffix = currentLineSuffix <> "\n" <> String.joinWith "\n" suffixLines
  
  { prefix: prefix
  , suffix: suffix
  , language: editorState.language
  , maxTokens: 500
  , temperature: 0.2  -- Lower temperature for more deterministic completions
  }

-- | Detect if FIM is appropriate for current context
shouldUseFIM :: EditorState -> Boolean
shouldUseFIM editorState = do
  let prefix = extractFIMContext editorState
  -- Use FIM if:
  -- 1. There's code after cursor (not just end-of-file completion)
  -- 2. Prefix suggests incomplete structure (open brace, function signature, etc.)
  let hasSuffix = String.length prefix.suffix > 0
  let hasIncompleteStructure = detectIncompleteStructure prefix.prefix
  
  hasSuffix && hasIncompleteStructure

-- | Detect incomplete code structures
detectIncompleteStructure :: String -> Boolean
detectIncompleteStructure prefix = do
  -- Check for patterns that suggest incomplete code:
  -- - Function signature without body
  -- - Open brace without closing
  -- - If/while/for without body
  -- - Class/interface without implementation
  
  let hasFunctionSignature = String.contains (String.Pattern "function ") prefix ||
                             String.contains (String.Pattern "=>") prefix ||
                             String.contains (String.Pattern "::") prefix
  
  let hasOpenBrace = (countChar prefix '{') > (countChar prefix '}')
  let hasOpenParen = (countChar prefix '(') > (countChar prefix ')')
  
  hasFunctionSignature || hasOpenBrace || hasOpenParen

-- | Count occurrences of character in string
countChar :: String -> Char -> Int
countChar str char = do
  let pattern = String.Pattern (String.singleton char)
  String.split pattern str # Array.length # (_ - 1)

-- | Convert FIM response to inline suggestion
fimResponseToSuggestion :: FIMResponse -> Position -> InlineSuggestion
fimResponseToSuggestion response position = do
  let completionLines = String.split (String.Pattern "\n") response.completion
  let endLine = position.line + Array.length completionLines - 1
  let endCol = case Array.last completionLines of
    Nothing -> position.column
    Just lastLine -> position.column + String.length lastLine
  
  { text: response.completion
  , range:
      { start: position
      , end: { line: endLine, column: endCol }
      }
  , confidence: response.confidence
  , alternatives: response.alternatives
  , completionKind: SnippetCompletion
  }
