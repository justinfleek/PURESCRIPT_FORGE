{-|
Module      : Forge.Format.Formatter
Description : Code Formatter

Code formatting utilities that integrate with external formatters
like prettier, biome, rustfmt, etc.

== Supported Languages

| Language   | Formatter      | Extension       |
|------------|----------------|-----------------|
| JavaScript | prettier/biome | .js, .jsx       |
| TypeScript | prettier/biome | .ts, .tsx       |
| JSON       | prettier/biome | .json           |
| HTML       | prettier       | .html           |
| CSS        | prettier       | .css, .scss     |
| Rust       | rustfmt        | .rs             |
| Go         | gofmt          | .go             |
| Python     | black          | .py             |
| Haskell    | ormolu         | .hs             |
| PureScript | purty          | .purs           |
-}
module Forge.Format.Formatter
  ( -- * Types
    FormatConfig
  , FormatResult
  , FormatterType(..)
    -- * Formatting
  , format
  , formatFile
  , formatFiles
    -- * Detection
  , detectLanguage
  , detectFormatter
  , isFormattable
    -- * Default Config
  , defaultConfig
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

-- | Available formatters
data FormatterType
  = Prettier
  | Biome
  | Rustfmt
  | Gofmt
  | Black
  | Ormolu
  | Purty
  | Custom String

derive instance eqFormatterType :: Eq FormatterType

instance showFormatterType :: Show FormatterType where
  show Prettier = "prettier"
  show Biome = "biome"
  show Rustfmt = "rustfmt"
  show Gofmt = "gofmt"
  show Black = "black"
  show Ormolu = "ormolu"
  show Purty = "purty"
  show (Custom s) = s

-- | Format configuration
type FormatConfig =
  { language :: Maybe String    -- Override language detection
  , indentSize :: Int           -- Spaces per indent
  , useTabs :: Boolean          -- Use tabs instead of spaces
  , printWidth :: Int           -- Max line width
  , formatter :: Maybe FormatterType  -- Override formatter
  }

-- | Format result
type FormatResult =
  { original :: String
  , formatted :: String
  , changed :: Boolean
  , formatter :: String
  }

-- ============================================================================
-- FFI
-- ============================================================================

foreign import runFormatterFFI :: String -> String -> Array String -> Aff (Either String String)
foreign import checkFormatterFFI :: String -> Aff Boolean

-- ============================================================================
-- DEFAULT CONFIG
-- ============================================================================

defaultConfig :: FormatConfig
defaultConfig =
  { language: Nothing
  , indentSize: 2
  , useTabs: false
  , printWidth: 100
  , formatter: Nothing
  }

-- ============================================================================
-- FORMATTING
-- ============================================================================

{-| Format code string.

Detects language and formatter automatically unless specified in config.
-}
format :: String -> FormatConfig -> Aff (Either String String)
format code config = do
  let lang = case config.language of
        Just l -> l
        Nothing -> "javascript"  -- Default
  
  let formatter = case config.formatter of
        Just f -> f
        Nothing -> detectFormatter lang
  
  -- Check if formatter is available
  available <- checkFormatterFFI (show formatter)
  if not available
    then pure $ Left ("Formatter not available: " <> show formatter)
    else do
      let args = buildFormatterArgs formatter config
      runFormatterFFI (show formatter) code args

{-| Format a file in place.

Reads the file, formats it, and writes it back.
-}
formatFile :: String -> Aff (Either String Unit)
formatFile path = do
  -- Read file
  readResult <- readFileFFI path
  case readResult of
    Left err -> pure $ Left err
    Right content -> do
      -- Detect language from extension
      let lang = detectLanguage path
      let config = defaultConfig { language = Just lang }
      
      -- Format
      formatResult <- format content config
      case formatResult of
        Left err -> pure $ Left err
        Right formatted ->
          if formatted == content
            then pure $ Right unit  -- No changes
            else writeFileFFI path formatted

{-| Format multiple files. -}
formatFiles :: Array String -> Aff (Either String Int)
formatFiles paths = do
  results <- traverseAff formatFile paths
  let successes = Array.length $ Array.filter isRight results
  pure $ Right successes
  where
    isRight (Right _) = true
    isRight (Left _) = false

-- ============================================================================
-- DETECTION
-- ============================================================================

{-| Detect language from file extension. -}
detectLanguage :: String -> String
detectLanguage path =
  let ext = getExtension path
  in case ext of
    ".js" -> "javascript"
    ".jsx" -> "javascript"
    ".ts" -> "typescript"
    ".tsx" -> "typescript"
    ".json" -> "json"
    ".html" -> "html"
    ".css" -> "css"
    ".scss" -> "scss"
    ".rs" -> "rust"
    ".go" -> "go"
    ".py" -> "python"
    ".hs" -> "haskell"
    ".purs" -> "purescript"
    ".md" -> "markdown"
    ".yaml" -> "yaml"
    ".yml" -> "yaml"
    _ -> "text"

{-| Detect formatter for a language. -}
detectFormatter :: String -> FormatterType
detectFormatter lang = case lang of
  "javascript" -> Prettier
  "typescript" -> Prettier
  "json" -> Prettier
  "html" -> Prettier
  "css" -> Prettier
  "scss" -> Prettier
  "markdown" -> Prettier
  "yaml" -> Prettier
  "rust" -> Rustfmt
  "go" -> Gofmt
  "python" -> Black
  "haskell" -> Ormolu
  "purescript" -> Purty
  _ -> Prettier  -- Default to prettier

{-| Check if a file can be formatted. -}
isFormattable :: String -> Boolean
isFormattable path =
  let lang = detectLanguage path
  in lang /= "text"

-- ============================================================================
-- HELPERS
-- ============================================================================

getExtension :: String -> String
getExtension path =
  let parts = String.split (String.Pattern ".") path
  in case Array.last parts of
    Just ext -> "." <> ext
    Nothing -> ""

buildFormatterArgs :: FormatterType -> FormatConfig -> Array String
buildFormatterArgs Prettier config =
  [ "--tab-width", show config.indentSize
  , "--print-width", show config.printWidth
  ] <> if config.useTabs then ["--use-tabs"] else []
buildFormatterArgs _ _ = []  -- Other formatters use defaults

foreign import readFileFFI :: String -> Aff (Either String String)
foreign import writeFileFFI :: String -> String -> Aff (Either String Unit)
foreign import traverseAff :: forall a b. (a -> Aff b) -> Array a -> Aff (Array b)
