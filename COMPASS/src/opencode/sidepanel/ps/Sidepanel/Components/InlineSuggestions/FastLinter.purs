{-|
Module      : Sidepanel.Components.InlineSuggestions.FastLinter
Description : Fast linting integration for real-time code feedback
Integrates fast linting tools (Biome, Ruff, ESLint) with code completion
for real-time feedback. Uses incremental linting and caching for speed.
-}
module Sidepanel.Components.InlineSuggestions.FastLinter where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Map as Map
import Data.Number as Number
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Class (liftEffect)
import Effect (Effect)
import Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes
  ( EditorState
  , Position
  , InlineSuggestion
  , Range
  )

-- | Lint diagnostic
type LintDiagnostic =
  { severity :: LintSeverity
  , message :: String
  , location :: { file :: String, line :: Int, column :: Int, endLine :: Int, endColumn :: Int }
  , rule :: String
  , fix :: Maybe LintFix
  }

-- | Lint severity
data LintSeverity
  = Error
  | Warning
  | Info
  | Hint

derive instance eqLintSeverity :: Eq LintSeverity

-- | Lint fix
type LintFix =
  { range :: { start :: Position, end :: Position }
  , replacement :: String
  , description :: String
  }

-- | Lint result
type LintResult =
  { diagnostics :: Array LintDiagnostic
  , errors :: Int
  , warnings :: Int
  , cached :: Boolean
  , duration :: Number  -- Milliseconds
  }

-- | Lint cache entry
type LintCacheEntry =
  { contentHash :: String
  , result :: LintResult
  , timestamp :: Number
  }

-- | Global lint cache (file path -> cache entry)
lintCacheRef :: Ref (Map.Map String LintCacheEntry)
lintCacheRef = unsafePerformEffect $ Ref.new Map.empty
  where
    foreign import unsafePerformEffect :: forall a. Effect a -> a

-- | Cache TTL in milliseconds (5 minutes)
cacheTTL :: Number
cacheTTL = 300000.0

-- | Fast lint file
lintFile :: EditorState -> Aff LintResult
lintFile editorState = do
  -- Determine linter based on language
  let linter = selectLinter editorState.language
  
  -- Check cache first (incremental linting)
  cacheHit <- checkCache editorState
  
  case cacheHit of
    Just cachedResult -> pure cachedResult
    Nothing -> do
      -- Run appropriate linter
      result <- case linter of
        Just l -> runLinter l editorState
        Nothing -> pure
          { diagnostics: []
          , errors: 0
          , warnings: 0
          , cached: false
          , duration: 0.0
          }
      
      -- Store in cache
      storeInCache editorState result
      
      pure result

-- | Check cache for existing lint result
checkCache :: EditorState -> Aff (Maybe LintResult)
checkCache editorState = do
  cache <- liftEffect $ Ref.read lintCacheRef
  currentTimeMs <- liftEffect getCurrentTime
  let currentTime = Number.fromInt currentTimeMs
  contentHash <- liftEffect $ hashContent editorState.content
  
  case Map.lookup editorState.filePath cache of
    Nothing -> pure Nothing
    Just entry -> do
      -- Check if cache entry is still valid (not expired and content matches)
      let age = currentTime - entry.timestamp
      let isValid = age < cacheTTL && entry.contentHash == contentHash
      
      if isValid
        then pure $ Just entry.result { cached = true }
        else pure Nothing

-- | Store lint result in cache
storeInCache :: EditorState -> LintResult -> Aff Unit
storeInCache editorState result = do
  contentHash <- liftEffect $ hashContent editorState.content
  timestampMs <- liftEffect getCurrentTime
  let timestamp = Number.fromInt timestampMs
  
  liftEffect $ Ref.modify_ (\cache ->
    Map.insert editorState.filePath
      { contentHash: contentHash
      , result: result
      , timestamp: timestamp
      }
      cache
  ) lintCacheRef

-- | Hash content for cache key (simple hash)
foreign import hashContent :: String -> Effect String

-- | Select appropriate linter for language
selectLinter :: String -> Maybe LinterType
selectLinter = case _ of
  "typescript" -> Just BiomeLinter
  "javascript" -> Just BiomeLinter
  "typescriptreact" -> Just BiomeLinter
  "javascriptreact" -> Just BiomeLinter
  "json" -> Just BiomeLinter
  "python" -> Just RuffLinter
  "purescript" -> Just PursTidyLinter
  "haskell" -> Just HLintLinter
  "lean4" -> Just LeanLinter
  _ -> Nothing

-- | Linter type
data LinterType
  = BiomeLinter
  | RuffLinter
  | PursTidyLinter
  | HLintLinter
  | LeanLinter
  | ESLintLinter

derive instance eqLinterType :: Eq LinterType

-- | Run linter
runLinter :: LinterType -> EditorState -> Aff LintResult
runLinter linter editorState = do
  startTime <- liftEffect getCurrentTime
  
  -- Call appropriate linter via FFI
  result <- case linter of
    BiomeLinter -> runBiomeLint editorState.filePath editorState.content
    RuffLinter -> runRuffLint editorState.filePath editorState.content
    PursTidyLinter -> runAlephLint editorState.filePath editorState.content  -- Use aleph-lint
    HLintLinter -> runAlephLint editorState.filePath editorState.content  -- Use aleph-lint
    LeanLinter -> runLeanLint editorState.filePath editorState.content
    ESLintLinter -> runESLintLint editorState.filePath editorState.content
  
  endTime <- liftEffect getCurrentTime
  let duration = Number.fromInt (endTime - startTime)
  
  case result of
    Left err -> pure
      { diagnostics: []
      , errors: 0
      , warnings: 0
      , cached: false
      , duration: duration
      }
    Right lintData -> pure
      { diagnostics: convertDiagnostics lintData.diagnostics editorState.filePath
      , errors: lintData.errors
      , warnings: lintData.warnings
      , cached: false  -- Set by checkCache/storeInCache
      , duration: duration
      }

-- | Convert linter diagnostics to our format
convertDiagnostics :: Array LinterDiagnostic -> String -> Array LintDiagnostic
convertDiagnostics diagnostics filePath = do
  Array.mapMaybe (convertDiagnostic filePath) diagnostics

-- | Convert single diagnostic
convertDiagnostic :: String -> LinterDiagnostic -> Maybe LintDiagnostic
convertDiagnostic filePath diagnostic = do
  -- This would parse the actual linter output format
  -- Simplified for now
  Just
    { severity: Warning  -- Would parse from diagnostic
    , message: fromMaybe "Lint issue" diagnostic.message
    , location:
        { file: filePath
        , line: fromMaybe 0 diagnostic.line
        , column: fromMaybe 0 diagnostic.column
        , endLine: fromMaybe (fromMaybe 0 diagnostic.line) diagnostic.endLine
        , endColumn: fromMaybe (fromMaybe 0 diagnostic.column) diagnostic.endColumn
        }
    , rule: fromMaybe "unknown" diagnostic.rule
    , fix: Nothing  -- Would parse fix if available
    }

-- | Linter diagnostic format (from FFI)
type LinterDiagnostic =
  { message :: Maybe String
  , line :: Maybe Int
  , column :: Maybe Int
  , endLine :: Maybe Int
  , endColumn :: Maybe Int
  , rule :: Maybe String
  }

-- | FFI imports
foreign import runBiomeLint :: String -> String -> Aff (Either String { diagnostics :: Array LinterDiagnostic, errors :: Int, warnings :: Int })
foreign import runRuffLint :: String -> String -> Aff (Either String { diagnostics :: Array LinterDiagnostic, errors :: Int, warnings :: Int })
foreign import runAlephLint :: String -> String -> Aff (Either String { diagnostics :: Array LinterDiagnostic, errors :: Int, warnings :: Int })
foreign import runLeanLint :: String -> String -> Aff (Either String { diagnostics :: Array LinterDiagnostic, errors :: Int, warnings :: Int })
foreign import runESLintLint :: String -> String -> Aff (Either String { diagnostics :: Array LinterDiagnostic, errors :: Int, warnings :: Int })
foreign import getCurrentTime :: Effect Int
foreign import hashContent :: String -> Effect String

-- | Import Effect.Class
import Effect.Class (liftEffect)

-- | Lint suggestion (combine linting with AI suggestions)
type LintedSuggestion =
  { suggestion :: InlineSuggestion
  , lintDiagnostics :: Array LintDiagnostic
  , passesLint :: Boolean
  }

-- | Validate suggestion against linter
validateSuggestion :: InlineSuggestion -> EditorState -> Aff LintedSuggestion
validateSuggestion suggestion editorState = do
  -- Apply suggestion to editor state
  let modifiedState = applySuggestion suggestion editorState
  
  -- Lint the modified code
  lintResult <- lintFile modifiedState
  
  -- Filter diagnostics that affect the suggestion
  let relevantDiagnostics = Array.filter (isInRange suggestion.range) lintResult.diagnostics
  
  pure
    { suggestion: suggestion
    , lintDiagnostics: relevantDiagnostics
    , passesLint: Array.length relevantDiagnostics == 0
    }

-- | Check if diagnostic is in suggestion range
isInRange :: Range -> LintDiagnostic -> Boolean
isInRange range diagnostic = do
  let loc = diagnostic.location
  -- Check if diagnostic overlaps with suggestion range
  loc.line >= range.start.line && loc.line <= range.end.line

-- | Apply suggestion to editor state
applySuggestion :: InlineSuggestion -> EditorState -> EditorState
applySuggestion suggestion editorState = do
  -- Insert suggestion text at range
  let lines = String.split (String.Pattern "\n") editorState.content
  -- Simplified - would properly insert text
  editorState { content = editorState.content <> suggestion.text }

