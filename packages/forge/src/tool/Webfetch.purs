{-|
Module      : Forge.Tool.Webfetch
Description : URL content fetching with format conversion
= Webfetch Tool

Fetch content from URLs with automatic format conversion.

== Coeffect Equation

@
  webfetch : WebfetchParams -> Graded Network WebfetchResult

  -- Requires network access for HTTP requests
@

== Formats

| Format   | Description                          |
|----------|--------------------------------------|
| markdown | HTML -> Markdown via turndown         |
| text     | HTML -> Plain text (strip tags)       |
| html     | Raw HTML response                    |

== Usage

@
  webfetch { url: "https://example.com", format: Just "markdown" }
@
-}
module Forge.Tool.Webfetch
  ( -- * Tool Interface
    WebfetchParams(..)
  , WebfetchResult(..)
  , execute
  , webfetchTool
    -- * Configuration
  , WebfetchConfig(..)
  , defaultConfig
    -- * Format Conversion
  , OutputFormat(..)
  ) where

import Prelude

import Data.Maybe (Maybe(..), maybe)
import Data.Either (Either(..))
import Data.String as String
import Data.Argonaut (Json, encodeJson, decodeJson, (.:), (.:?), printJsonDecodeError)
import Effect.Aff (Aff)

-- ============================================================================
-- CONFIGURATION
-- ============================================================================

type WebfetchConfig =
  { maxResponseSize :: Int   -- Maximum response in bytes (5MB)
  , defaultTimeout :: Int    -- Default timeout in ms
  , maxTimeout :: Int        -- Maximum timeout in ms
  , userAgent :: String      -- User agent string
  }

defaultConfig :: WebfetchConfig
defaultConfig =
  { maxResponseSize: 5 * 1024 * 1024
  , defaultTimeout: 30000
  , maxTimeout: 120000
  , userAgent: "Mozilla/5.0 (compatible; Forge/1.0)"
  }

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Webfetch tool parameters.
type WebfetchParams =
  { url :: String
  , format :: Maybe String
  , timeout :: Maybe Int
  }

data OutputFormat
  = Markdown
  | Text
  | Html

derive instance eqOutputFormat :: Eq OutputFormat

instance showOutputFormat :: Show OutputFormat where
  show Markdown = "markdown"
  show Text = "text"
  show Html = "html"

parseFormat :: Maybe String -> OutputFormat
parseFormat = case _ of
  Just "text" -> Text
  Just "html" -> Html
  _ -> Markdown

type WebfetchResult =
  { content :: String
  , contentType :: String
  , statusCode :: Int
  , url :: String
  }

-- | Tool result type
type ToolResult =
  { title :: String
  , output :: String
  , metadata :: Json
  , attachments :: Maybe (Array Json)
  }

-- | Tool context
type ToolContext = 
  { workspaceRoot :: String
  }

-- | Tool info
type ToolInfo =
  { id :: String
  , description :: String
  , parameters :: Json
  , execute :: Json -> ToolContext -> Aff ToolResult
  , formatValidationError :: Maybe (Json -> String)
  }

-- ============================================================================
-- EXECUTION
-- ============================================================================

execute :: WebfetchParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Validate URL
  case validateUrl params.url of
    Left err -> pure $ mkErrorResult err
    Right url -> executeImpl params { url = url } ctx

executeImpl :: WebfetchParams -> ToolContext -> Aff ToolResult
executeImpl params _ctx = do
  let format = parseFormat params.format
  let timeout = maybe defaultConfig.defaultTimeout (\t -> min (t * 1000) defaultConfig.maxTimeout) params.timeout
  
  -- Fetch URL content via FFI
  result <- fetchUrlFFI params.url timeout defaultConfig.userAgent
  
  case result of
    Left err -> pure $ mkErrorResult err
    Right response -> do
      -- Convert based on format
      let converted = case format of
            Markdown -> convertToMarkdownFFI response.content
            Text -> extractTextFFI response.content
            Html -> response.content
      
      pure
        { title: params.url
        , metadata: encodeJson
            { url: params.url
            , format: show format
            , statusCode: response.statusCode
            , contentType: response.contentType
            }
        , output: truncateContent converted
        , attachments: Nothing
        }

-- | FFI for fetching URL
foreign import fetchUrlFFI :: String -> Int -> String -> Aff (Either String { content :: String, statusCode :: Int, contentType :: String })

-- | FFI for HTML to Markdown conversion
foreign import convertToMarkdownFFI :: String -> String

-- | FFI for HTML text extraction
foreign import extractTextFFI :: String -> String

-- | Truncate content if too large
truncateContent :: String -> String
truncateContent content =
  if String.length content > defaultConfig.maxResponseSize
    then String.take defaultConfig.maxResponseSize content <> "\n\n[Content truncated...]"
    else content

-- | Validate URL format
validateUrl :: String -> Either String String
validateUrl url
  | String.take 7 url == "http://" = Right (upgradeToHttps url)
  | String.take 8 url == "https://" = Right url
  | otherwise = Left "URL must start with http:// or https://"
  where
    upgradeToHttps u = "https://" <> String.drop 7 u

-- ============================================================================
-- TOOL REGISTRATION
-- ============================================================================

webfetchTool :: ToolInfo
webfetchTool =
  { id: "webfetch"
  , description: "Fetch content from URL with format conversion"
  , parameters: webfetchSchema
  , execute: \json ctx ->
      case decodeWebfetchParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> execute params ctx
  , formatValidationError: Nothing
  }

webfetchSchema :: Json
webfetchSchema = encodeJson
  { "type": "object"
  , "properties":
      { "url":
          { "type": "string"
          , "description": "The URL to fetch content from"
          }
      , "format":
          { "type": "string"
          , "description": "The format to return the content in (text, markdown, or html). Defaults to markdown."
          , "enum": ["text", "markdown", "html"]
          }
      , "timeout":
          { "type": "number"
          , "description": "Optional timeout in seconds (max 120)"
          }
      }
  , "required": ["url"]
  }

decodeWebfetchParams :: Json -> Either String WebfetchParams
decodeWebfetchParams json =
  case decodeWebfetchParamsImpl json of
    Left err -> Left (printJsonDecodeError err)
    Right result -> Right result
  where
    decodeWebfetchParamsImpl j = do
      obj <- decodeJson j
      url <- obj .: "url"
      format <- obj .:? "format"
      timeout <- obj .:? "timeout"
      pure { url, format, timeout }

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Webfetch Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }
