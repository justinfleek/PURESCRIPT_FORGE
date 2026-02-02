{-|
Module      : Tool.Webfetch
Description : URL content fetching with format conversion
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Webfetch Tool

Fetch content from URLs with automatic format conversion.

== Coeffect Equation

@
  webfetch : WebfetchParams → Graded Network WebfetchResult

  -- Requires network access for HTTP requests
@

== Formats

| Format   | Description                          |
|----------|--------------------------------------|
| markdown | HTML → Markdown via turndown         |
| text     | HTML → Plain text (strip tags)       |
| html     | Raw HTML response                    |

== Usage

@
  webfetch { url: "https://example.com", format: Just "markdown" }
@
-}
module Tool.Webfetch
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
  , convertToMarkdown
  , extractText
    -- * Coeffects
  , webfetchCoeffect
  ) where

import Prelude

import Data.Maybe (Maybe(..), maybe)
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Argonaut (Json, encodeJson, decodeJson)
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Aleph.Coeffect (Resource(..), network)
import Bridge.FFI.Node.Fetch as Fetch
import Effect.Class (liftEffect)

-- ════════════════════════════════════════════════════════════════════════════
-- CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════

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
  , userAgent: "Mozilla/5.0 (compatible; OpenCode/1.0)"
  }

-- ════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ════════════════════════════════════════════════════════════════════════════

{-| Webfetch tool parameters.

@
  record WebfetchParams where
    url     : String
    format  : Maybe String   -- "markdown" | "text" | "html"
    timeout : Maybe Int      -- Timeout in seconds
@
-}
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
derive instance genericOutputFormat :: Generic OutputFormat _

instance showOutputFormat :: Show OutputFormat where
  show = genericShow

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

-- ════════════════════════════════════════════════════════════════════════════
-- EXECUTION
-- ════════════════════════════════════════════════════════════════════════════

execute :: WebfetchParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Validate URL
  case validateUrl params.url of
    Left err -> pure $ mkErrorResult err
    Right url -> executeImpl params { url = url } ctx

executeImpl :: WebfetchParams -> ToolContext -> Aff ToolResult
executeImpl params _ctx = do
  let format = parseFormat params.format
  
  -- Build request options
  let options =
        { method: "GET"
        , headers:
            [ { key: "Accept", value: acceptHeader format }
            , { key: "User-Agent", value: defaultConfig.userAgent }
            ]
        , body: Nothing
        }
  
  -- Make HTTP request via Fetch FFI
  result <- Fetch.fetch params.url options
  
  case result of
    Left err -> 
      pure $ mkErrorResult ("Fetch failed: " <> err)
    
    Right response -> do
      -- Check response status
      statusCode <- liftEffect $ Fetch.status response
      isOk <- liftEffect $ Fetch.ok response
      
      if not isOk
        then pure $ mkErrorResult ("HTTP " <> show statusCode <> " error")
        else do
          -- Get response text
          textResult <- Fetch.text response
          case textResult of
            Left err -> 
              pure $ mkErrorResult ("Failed to read response: " <> err)
            
            Right content -> do
              -- Get content type
              headers <- liftEffect $ Fetch.getHeaders response
              contentType <- liftEffect $ Fetch.getHeader headers "content-type"
              
              -- Convert based on format
              let converted = case format of
                    Markdown -> convertToMarkdown content
                    Text -> extractText content
                    Html -> content
              
              pure
                { title: params.url
                , metadata: encodeJson
                    { url: params.url
                    , format: show format
                    , statusCode
                    , contentType: contentType # maybe "unknown" identity
                    }
                , output: truncateContent converted
                , attachments: Nothing
                }

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

-- ════════════════════════════════════════════════════════════════════════════
-- FORMAT CONVERSION
-- ════════════════════════════════════════════════════════════════════════════

{-| Convert HTML to Markdown.

Uses turndown-style conversion:
- Headings → # syntax
- Links → [text](url)
- Lists → - items
- Code → ``` blocks
-}
convertToMarkdown :: String -> String
convertToMarkdown html =
  -- TODO: Implement HTML → Markdown conversion
  html

{-| Extract plain text from HTML.

Removes:
- script, style, noscript elements
- All HTML tags
- Extra whitespace
-}
extractText :: String -> String
extractText html =
  -- TODO: Implement HTML → text extraction
  html

-- | Build Accept header for format
acceptHeader :: OutputFormat -> String
acceptHeader = case _ of
  Markdown -> "text/markdown;q=1.0, text/html;q=0.9, text/plain;q=0.8"
  Text -> "text/plain;q=1.0, text/html;q=0.8"
  Html -> "text/html;q=1.0, application/xhtml+xml;q=0.9"

-- ════════════════════════════════════════════════════════════════════════════
-- COEFFECTS
-- ════════════════════════════════════════════════════════════════════════════

webfetchCoeffect :: Resource
webfetchCoeffect = network

-- ════════════════════════════════════════════════════════════════════════════
-- TOOL REGISTRATION
-- ════════════════════════════════════════════════════════════════════════════

webfetchTool :: ToolInfo
webfetchTool =
  { id: "webfetch"
  , description: "Fetch content from URL with format conversion"
  , parameters: webfetchSchema
  , execute: \json ctx ->
      case decodeJson json of
        Left err -> pure $ mkErrorResult (show err)
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

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Webfetch Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }
