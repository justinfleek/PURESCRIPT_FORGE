{-|
Module      : Tool.Codesearch
Description : External code search via Exa API
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

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

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Argonaut (Json, class EncodeJson, encodeJson, decodeJson)
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Aleph.Coeffect (Resource(..))

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
  
  -- 3. Make HTTP request
  -- TODO: HTTP FFI call to Exa API
  
  -- 4. Parse SSE response
  -- TODO: Parse "data: " lines
  
  -- 5. Return result
  pure
    { title: "Code search: " <> params.query
    , metadata: encodeJson
        { query: params.query
        , tokensNum: tokens
        }
    , output: "TODO: Implement Exa API call"
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

codesearchSchema :: { type :: String }
codesearchSchema = { type: "object" }

decodeCodeSearchParams :: Json -> Either String CodeSearchParams
decodeCodeSearchParams _ = notImplemented "decodeCodeSearchParams"

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Code Search Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatValidationError :: Json -> String
formatValidationError _ = "Invalid codesearch parameters"

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
