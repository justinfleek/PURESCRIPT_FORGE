{-|
Module      : Tool.Codesearch
Description : External code search via Exa API
= Code Search Tool

Searches for code context, API documentation, and library examples
using the Exa code search API. Useful for finding up-to-date
documentation and usage patterns.

== Coeffect Equation

@
  codesearch : CodeSearchParams -> Graded Network ToolResult

  -- Requires:
  -- 1. Network access to Exa API
@

== Use Cases

1. Finding API documentation and examples
2. Understanding library usage patterns
3. Discovering SDK configuration options
4. Getting code snippets for frameworks

== Token Budget

| tokensNum | Use Case                           |
|-----------|-----------------------------------|
| 1000-3000 | Focused queries, single concept    |
| 5000      | Default, balanced coverage         |
| 10000+    | Comprehensive documentation        |
| 50000     | Maximum, full API reference        |

== Example Queries

- "React useState hook examples"
- "Python pandas dataframe filtering"
- "Express.js middleware error handling"
- "Next.js partial prerendering configuration"
-}
module Tool.Codesearch
  ( -- * Tool Interface
    CodeSearchParams(..)
  , execute
  , codesearchTool
    -- * API Types
  , McpRequest(..)
  , McpResponse(..)
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Argonaut (Json, class EncodeJson, encodeJson, decodeJson, (.:), (.:?), jsonParser, stringify)
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo, ToolMetadata(..))
import Aleph.Coeffect (Resource(..))
-- | FFI for HTTP POST with timeout
foreign import httpPostWithTimeout :: Int -> String -> String -> Aff (Either String { statusCode :: Int, body :: String })

-- ============================================================================
-- CONFIGURATION
-- ============================================================================

-- | Exa API base URL
apiBaseUrl :: String
apiBaseUrl = "https://mcp.exa.ai"

-- | API endpoint
apiEndpoint :: String
apiEndpoint = "/mcp"

-- | Request timeout in milliseconds
requestTimeout :: Int
requestTimeout = 30000

-- | Default token count
defaultTokens :: Int
defaultTokens = 5000

-- | Minimum tokens
minTokens :: Int
minTokens = 1000

-- | Maximum tokens
maxTokens :: Int
maxTokens = 50000

-- ============================================================================
-- TYPES
-- ============================================================================

{-| Parameters for codesearch tool.

@
  record CodeSearchParams where
    query     : String   -- Search query for APIs/libraries
    tokensNum : Int      -- Number of tokens to return (1000-50000)
@
-}
type CodeSearchParams =
  { query :: String
  , tokensNum :: Maybe Int
  }

{-| MCP request to Exa API. -}
type McpRequest =
  { jsonrpc :: String
  , id :: Int
  , method :: String
  , params ::
      { name :: String
      , arguments ::
          { query :: String
          , tokensNum :: Int
          }
      }
  }

{-| MCP response from Exa API. -}
type McpResponse =
  { jsonrpc :: String
  , result ::
      { content :: Array { type :: String, text :: String }
      }
  }

-- ============================================================================
-- TOOL INTERFACE
-- ============================================================================

{-| Execute codesearch tool.

Searches for code context using Exa's code search API.
-}
execute :: CodeSearchParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Validate and normalize token count
  let tokens = clamp minTokens maxTokens (fromMaybe defaultTokens params.tokensNum)
  
  -- 2. Build MCP request
  let request = buildRequest params.query tokens
  let requestBodyStr = stringify (encodeJson request)
  
  -- 3. Make HTTP request to Exa API
  httpResult <- httpPostWithTimeout requestTimeout (apiBaseUrl <> apiEndpoint) requestBodyStr
  case httpResult of
    Left err -> pure $ mkErrorResult ("HTTP request failed: " <> err)
    Right response -> do
      -- 4. Parse SSE response (or JSON response)
      case parseResponse response.body of
        Left err -> pure $ mkErrorResult ("Parse error: " <> err)
        Right results -> do
          -- 5. Format and return result
          let output = formatCodeSearchResults params.query results
          pure
            { title: "Code search: " <> params.query
            , metadata: CodesearchMetadata
                { query: params.query
                , tokensNum: tokens
                , resultsCount: Array.length results
                }
            , output
            , attachments: Nothing
            }
  where
    fromMaybe :: forall a. a -> Maybe a -> a
    fromMaybe def Nothing = def
    fromMaybe _ (Just x) = x
    
    clamp :: Int -> Int -> Int -> Int
    clamp lo hi x
      | x < lo = lo
      | x > hi = hi
      | otherwise = x

{-| Build MCP request. -}
buildRequest :: String -> Int -> McpRequest
buildRequest query tokens =
  { jsonrpc: "2.0"
  , id: 1
  , method: "tools/call"
  , params:
      { name: "get_code_context_exa"
      , arguments:
          { query
          , tokensNum: tokens
          }
      }
  }

{-| Tool registration. -}
codesearchTool :: ToolInfo
codesearchTool =
  { id: "codesearch"
  , description: codesearchDescription
  , parameters: encodeJson codesearchSchema
  , execute: \json ctx ->
      case decodeCodeSearchParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> execute params ctx
  , formatValidationError: Just formatValidationError
  }

-- ============================================================================
-- HELPERS
-- ============================================================================

codesearchDescription :: String
codesearchDescription =
  "Search for code context, API documentation, and library examples. " <>
  "Use this for finding up-to-date documentation, usage patterns, " <>
  "and SDK configuration."

codesearchSchema :: Json
codesearchSchema = encodeJson
  { type: "object"
  , properties:
      { query: { type: "string", description: "Search query for APIs/libraries" }
      , tokensNum: { type: "integer", description: "Number of tokens to return (1000-50000)", minimum: 1000, maximum: 50000, default: 5000 }
      }
  , required: ["query"]
  }

decodeCodeSearchParams :: Json -> Either String CodeSearchParams
decodeCodeSearchParams json = do
  obj <- decodeJson json
  query <- obj .: "query" >>= decodeJson
  tokensNum <- (obj .:? "tokensNum" >>= \mb -> pure (mb >>= decodeJson))
  pure { query, tokensNum }

-- | Parse response from Exa API (handles both JSON and SSE)
parseResponse :: String -> Either String (Array { type :: String, text :: String })
parseResponse body =
  -- Try parsing as JSON first
  case jsonParser body of
    Right json -> parseJsonResponse json
    Left _ -> parseSseResponse body
  where
    jsonParser :: String -> Either String Json
    jsonParser = jsonParserImpl
    
    foreign import jsonParserImpl :: String -> Either String Json

-- | Parse JSON response
parseJsonResponse :: Json -> Either String (Array { type :: String, text :: String })
parseJsonResponse json = do
  obj <- decodeJson json
  result <- obj .: "result"
  content <- result .: "content"
  decodeJson content

-- | Parse SSE (Server-Sent Events) response
parseSseResponse :: String -> Either String (Array { type :: String, text :: String })
parseSseResponse body =
  let lines = String.split (String.Pattern "\n") body
      dataLines = Array.filter (\line -> String.startsWith (String.Pattern "data: ") line) lines
      parsed = Array.mapMaybe parseSseLine dataLines
  in Right parsed
  where
    parseSseLine :: String -> Maybe { type :: String, text :: String }
    parseSseLine line =
      let content = String.drop 6 line  -- Remove "data: " prefix
      in case jsonParser content of
        Right json -> case decodeJson json of
          Right obj -> do
            text <- obj .:? "text" >>= \mb -> pure (mb >>= decodeJson)
            pure { type: "text", text: fromMaybe "" text }
          Left _ -> Nothing
        Left _ -> Just { type: "text", text: content }

-- | Format code search results for output
formatCodeSearchResults :: String -> Array { type :: String, text :: String } -> String
formatCodeSearchResults query results =
  if Array.null results
  then "No code context found for: " <> query
  else "Found " <> show (Array.length results) <> " code context result(s) for: " <> query <> "\n\n" <>
       String.joinWith "\n\n---\n\n" (Array.mapWithIndex formatResult results)
  where
    formatResult idx result =
      show (idx + 1) <> ". [" <> result.type <> "]\n" <>
      String.take 500 result.text <> (if String.length result.text > 500 then "..." else "")

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Code Search Error"
  , metadata: ErrorMetadata { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatValidationError :: Json -> String
formatValidationError _ = "Invalid codesearch parameters"

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
