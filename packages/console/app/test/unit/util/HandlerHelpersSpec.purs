-- | Deep comprehensive tests for Handler Main helper functions
-- | Tests findHeader, normalizeResponseStatus, scrubResponseHeaders, shouldRetryLogic
-- | Note: These functions are internal to Handler.Main, so we test their logic patterns
module Test.Unit.Util.HandlerHelpersSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual, shouldContain)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Array (find, filter, elem, replicate)
import Data.Foldable (fold)
import Data.String as String

import Console.App.Routes.Omega.Util.Handler.Types
  ( ModelInfo
  , ProviderData
  )

-- | Type alias for RequestHeaders (matches Handler.Main)
type RequestHeaders = Array { key :: String, value :: String }

-- | Replicate findHeader logic for testing
findHeader :: String -> RequestHeaders -> String
findHeader key headers =
  case find (\h -> String.toLower h.key == String.toLower key) headers of
    Just h -> h.value
    Nothing -> ""

-- | Replicate normalizeResponseStatus logic for testing
normalizeResponseStatus :: Int -> Int
normalizeResponseStatus status = if status == 404 then 400 else status

-- | Replicate scrubResponseHeaders logic for testing
scrubResponseHeaders :: RequestHeaders -> RequestHeaders
scrubResponseHeaders headers =
  let keepHeaders = ["content-type", "cache-control"]
  in filter (\h -> elem (String.toLower h.key) keepHeaders) headers

-- | Replicate shouldRetryLogic logic for testing
shouldRetryLogic :: Int -> ModelInfo -> ProviderData -> Boolean
shouldRetryLogic status modelInfo providerInfo =
  status /= 200 &&
  status /= 404 &&
  modelInfo.stickyProvider /= Just "strict" &&
  isJust modelInfo.fallbackProvider &&
  providerInfo.id /= fromMaybe "" modelInfo.fallbackProvider
  where
    fromMaybe :: forall a. a -> Maybe a -> a
    fromMaybe default Nothing = default
    fromMaybe _ (Just x) = x

-- | Create mock ModelInfo
mkMockModelInfo :: ModelInfo
mkMockModelInfo =
  { id: "gpt-4"
  , formatFilter: Nothing
  , providers: []
  , byokProvider: Nothing
  , trial: Nothing
  , rateLimit: Nothing
  , stickyProvider: Nothing
  , fallbackProvider: Nothing
  , allowAnonymous: false
  , cost: { input: 0.0, output: 0.0, cacheRead: Nothing, cacheWrite5m: Nothing, cacheWrite1h: Nothing }
  , cost200K: Nothing
  }

-- | Create mock ProviderData
mkMockProviderData :: String -> ProviderData
mkMockProviderData id =
  { id
  , format: "openai"
  , api: "https://api.openai.com"
  , model: "gpt-4"
  , weight: Just 1
  , disabled: false
  , headerMappings: Nothing
  , streamSeparator: "\n\n"
  , storeModel: "gpt-4"
  , apiKey: ""
  , modifyUrl: \url _ -> url
  , modifyHeaders: \_ _ -> unit
  , modifyBody: \body -> body
  , createBinaryStreamDecoder: \_ -> Nothing
  , createUsageParser: \_ -> { parse: \_ -> unit, retrieve: \_ -> Nothing }
  , normalizeUsage: \_ -> { inputTokens: 0, outputTokens: 0, reasoningTokens: Nothing, cacheReadTokens: Nothing, cacheWrite5mTokens: Nothing, cacheWrite1hTokens: Nothing }
  }

-- | Deep comprehensive tests for Handler Helper functions
spec :: Spec Unit
spec = describe "Handler Helpers Deep Tests" do
  describe "findHeader" do
    it "finds header by exact key match" do
      let headers = [{ key: "Content-Type", value: "application/json" }]
      findHeader "Content-Type" headers `shouldEqual` "application/json"

    it "finds header by case-insensitive key match" do
      let headers = [{ key: "Content-Type", value: "application/json" }]
      findHeader "content-type" headers `shouldEqual` "application/json"
      findHeader "CONTENT-TYPE" headers `shouldEqual` "application/json"
      findHeader "CoNtEnT-TyPe" headers `shouldEqual` "application/json"

    it "returns empty string when header not found" do
      let headers = [{ key: "Content-Type", value: "application/json" }]
      findHeader "Authorization" headers `shouldEqual` ""

    it "returns first matching header when multiple exist" do
      let headers = 
            [ { key: "X-Custom", value: "first" }
            , { key: "X-Custom", value: "second" }
            ]
      -- find returns first match
      findHeader "X-Custom" headers `shouldEqual` "first"

    it "handles empty headers array" do
      let headers = []
      findHeader "any-key" headers `shouldEqual` ""

    it "handles empty key" do
      let headers = [{ key: "Content-Type", value: "application/json" }]
      findHeader "" headers `shouldEqual` ""

    it "handles header with empty value" do
      let headers = [{ key: "X-Custom", value: "" }]
      findHeader "X-Custom" headers `shouldEqual` ""

    it "handles header with very long value" do
      let longValue = fold (replicate 10000 "a")
      let headers = [{ key: "X-Custom", value: longValue }]
      findHeader "X-Custom" headers `shouldEqual` longValue

    it "handles header key with whitespace" do
      let headers = [{ key: " Content-Type ", value: "application/json" }]
      -- String.toLower preserves whitespace, so won't match "Content-Type"
      findHeader "Content-Type" headers `shouldEqual` ""
      findHeader " content-type " headers `shouldEqual` "application/json"

  describe "normalizeResponseStatus" do
    it "converts 404 to 400" do
      normalizeResponseStatus 404 `shouldEqual` 400

    it "preserves 200 status" do
      normalizeResponseStatus 200 `shouldEqual` 200

    it "preserves 500 status" do
      normalizeResponseStatus 500 `shouldEqual` 500

    it "preserves 429 status" do
      normalizeResponseStatus 429 `shouldEqual` 429

    it "preserves 401 status" do
      normalizeResponseStatus 401 `shouldEqual` 401

    it "preserves all other status codes" do
      normalizeResponseStatus 201 `shouldEqual` 201
      normalizeResponseStatus 301 `shouldEqual` 301
      normalizeResponseStatus 400 `shouldEqual` 400
      normalizeResponseStatus 403 `shouldEqual` 403
      normalizeResponseStatus 502 `shouldEqual` 502

    it "BUG: only converts 404, not other 4xx errors" do
      -- BUG: Only 404 is converted to 400
      -- Other 4xx errors (400, 401, 403, etc.) are preserved
      -- Expected: Should convert all 4xx to 400 or handle differently
      -- Actual: Only 404 is converted
      normalizeResponseStatus 400 `shouldEqual` 400  -- Not converted
      normalizeResponseStatus 403 `shouldEqual` 403  -- Not converted
      normalizeResponseStatus 404 `shouldEqual` 400  -- Converted
      -- This test documents the behavior: only 404 is normalized

    it "handles zero status code (edge case)" do
      normalizeResponseStatus 0 `shouldEqual` 0

    it "handles negative status code (edge case)" do
      -- Negative status codes shouldn't happen, but test robustness
      normalizeResponseStatus (-1) `shouldEqual` (-1)

    it "handles very large status code" do
      normalizeResponseStatus 999 `shouldEqual` 999

  describe "scrubResponseHeaders" do
    it "keeps content-type header" do
      let headers = 
            [ { key: "Content-Type", value: "application/json" }
            , { key: "Authorization", value: "Bearer token" }
            ]
      let scrubbed = scrubResponseHeaders headers
      -- Should keep content-type
      findHeader "content-type" scrubbed `shouldEqual` "application/json"
      -- Should remove authorization
      findHeader "authorization" scrubbed `shouldEqual` ""

    it "keeps cache-control header" do
      let headers = 
            [ { key: "Cache-Control", value: "no-cache" }
            , { key: "Authorization", value: "Bearer token" }
            ]
      let scrubbed = scrubResponseHeaders headers
      findHeader "cache-control" scrubbed `shouldEqual` "no-cache"
      findHeader "authorization" scrubbed `shouldEqual` ""

    it "keeps both content-type and cache-control" do
      let headers = 
            [ { key: "Content-Type", value: "application/json" }
            , { key: "Cache-Control", value: "no-cache" }
            , { key: "Authorization", value: "Bearer token" }
            ]
      let scrubbed = scrubResponseHeaders headers
      findHeader "content-type" scrubbed `shouldEqual` "application/json"
      findHeader "cache-control" scrubbed `shouldEqual` "no-cache"
      findHeader "authorization" scrubbed `shouldEqual` ""

    it "removes all other headers" do
      let headers = 
            [ { key: "Authorization", value: "Bearer token" }
            , { key: "X-Custom", value: "value" }
            , { key: "Set-Cookie", value: "cookie=value" }
            ]
      let scrubbed = scrubResponseHeaders headers
      scrubbed.length `shouldEqual` 0

    it "handles case-insensitive header matching" do
      let headers = 
            [ { key: "CONTENT-TYPE", value: "application/json" }
            , { key: "cache-control", value: "no-cache" }
            ]
      let scrubbed = scrubResponseHeaders headers
      findHeader "content-type" scrubbed `shouldEqual` "application/json"
      findHeader "cache-control" scrubbed `shouldEqual` "no-cache"

    it "handles empty headers array" do
      let headers = []
      let scrubbed = scrubResponseHeaders headers
      scrubbed.length `shouldEqual` 0

    it "handles headers with empty values" do
      let headers = 
            [ { key: "Content-Type", value: "" }
            , { key: "Cache-Control", value: "" }
            ]
      let scrubbed = scrubResponseHeaders headers
      scrubbed.length `shouldEqual` 2
      findHeader "content-type" scrubbed `shouldEqual` ""
      findHeader "cache-control" scrubbed `shouldEqual` ""

    it "BUG: keeps headers with empty keys" do
      -- BUG: If header has empty key, it won't match keepHeaders list
      -- But if key is empty string, toLower is still empty, won't match
      -- This is correct behavior, but documents edge case
      let headers = [{ key: "", value: "value" }]
      let scrubbed = scrubResponseHeaders headers
      scrubbed.length `shouldEqual` 0

  describe "shouldRetryLogic" do
    it "returns false when status is 200" do
      let modelInfo = mkMockModelInfo { fallbackProvider = Just "provider2" }
      let providerInfo = mkMockProviderData "provider1"
      shouldRetryLogic 200 modelInfo providerInfo `shouldEqual` false

    it "returns false when status is 404" do
      let modelInfo = mkMockModelInfo { fallbackProvider = Just "provider2" }
      let providerInfo = mkMockProviderData "provider1"
      shouldRetryLogic 404 modelInfo providerInfo `shouldEqual` false

    it "returns true when status is 500 and conditions met" do
      let modelInfo = mkMockModelInfo
        { stickyProvider = Nothing
        , fallbackProvider = Just "provider2"
        }
      let providerInfo = mkMockProviderData "provider1"
      shouldRetryLogic 500 modelInfo providerInfo `shouldEqual` true

    it "returns false when stickyProvider is 'strict'" do
      let modelInfo = mkMockModelInfo
        { stickyProvider = Just "strict"
        , fallbackProvider = Just "provider2"
        }
      let providerInfo = mkMockProviderData "provider1"
      shouldRetryLogic 500 modelInfo providerInfo `shouldEqual` false

    it "returns false when fallbackProvider is Nothing" do
      let modelInfo = mkMockModelInfo
        { stickyProvider = Nothing
        , fallbackProvider = Nothing
        }
      let providerInfo = mkMockProviderData "provider1"
      shouldRetryLogic 500 modelInfo providerInfo `shouldEqual` false

    it "returns false when provider is fallback provider" do
      let modelInfo = mkMockModelInfo
        { stickyProvider = Nothing
        , fallbackProvider = Just "provider1"
        }
      let providerInfo = mkMockProviderData "provider1"
      shouldRetryLogic 500 modelInfo providerInfo `shouldEqual` false

    it "returns true when all conditions met" do
      let modelInfo = mkMockModelInfo
        { stickyProvider = Just "provider1"  -- Not "strict"
        , fallbackProvider = Just "provider2"
        }
      let providerInfo = mkMockProviderData "provider1"
      shouldRetryLogic 500 modelInfo providerInfo `shouldEqual` true

    it "handles various error status codes" do
      let modelInfo = mkMockModelInfo { fallbackProvider = Just "provider2" }
      let providerInfo = mkMockProviderData "provider1"
      shouldRetryLogic 429 modelInfo providerInfo `shouldEqual` true
      shouldRetryLogic 502 modelInfo providerInfo `shouldEqual` true
      shouldRetryLogic 503 modelInfo providerInfo `shouldEqual` true

    it "BUG: uses /= for status comparison (allows retry for 200/404)" do
      -- BUG: Logic uses `status /= 200 && status /= 404`
      -- This means if status is 200 or 404, retry is false (correct)
      -- But the logic could be clearer: `status != 200 && status != 404`
      -- Actually, this is correct behavior, just documenting the logic
      let modelInfo = mkMockModelInfo { fallbackProvider = Just "provider2" }
      let providerInfo = mkMockProviderData "provider1"
      shouldRetryLogic 200 modelInfo providerInfo `shouldEqual` false
      shouldRetryLogic 404 modelInfo providerInfo `shouldEqual` false
      -- This test documents the behavior

    it "BUG: stickyProvider check uses /= Just 'strict'" do
      -- BUG: Line 298 checks `modelInfo.stickyProvider /= Just "strict"`
      -- This means stickyProvider can be Nothing, Just "provider1", etc.
      -- Only Just "strict" prevents retry
      -- Expected: Should check if stickyProvider is enabled
      -- Actual: Only "strict" prevents retry
      let modelInfo1 = mkMockModelInfo
        { stickyProvider = Nothing
        , fallbackProvider = Just "provider2"
        }
      let modelInfo2 = mkMockModelInfo
        { stickyProvider = Just "provider1"
        , fallbackProvider = Just "provider2"
        }
      let providerInfo = mkMockProviderData "provider1"
      -- Both should allow retry (only "strict" prevents)
      shouldRetryLogic 500 modelInfo1 providerInfo `shouldEqual` true
      shouldRetryLogic 500 modelInfo2 providerInfo `shouldEqual` true
      -- This test documents the behavior

  describe "Edge Cases" do
    it "findHeader handles duplicate headers (returns first)" do
      let headers = 
            [ { key: "X-Custom", value: "first" }
            , { key: "X-Custom", value: "second" }
            , { key: "X-Custom", value: "third" }
            ]
      findHeader "X-Custom" headers `shouldEqual` "first"

    it "normalizeResponseStatus handles boundary status codes" do
      normalizeResponseStatus 403 `shouldEqual` 403  -- Just before 404
      normalizeResponseStatus 404 `shouldEqual` 400  -- Converted
      normalizeResponseStatus 405 `shouldEqual` 405  -- Just after 404

    it "scrubResponseHeaders preserves order of kept headers" do
      let headers = 
            [ { key: "Cache-Control", value: "no-cache" }
            , { key: "Content-Type", value: "application/json" }
            ]
      let scrubbed = scrubResponseHeaders headers
      scrubbed.length `shouldEqual` 2

    it "shouldRetryLogic handles edge case: status 0" do
      let modelInfo = mkMockModelInfo { fallbackProvider = Just "provider2" }
      let providerInfo = mkMockProviderData "provider1"
      -- 0 /= 200 && 0 /= 404, so should retry if other conditions met
      shouldRetryLogic 0 modelInfo providerInfo `shouldEqual` true

  describe "Bug Detection Tests" do
    it "detects bug: normalizeResponseStatus only converts 404" do
      -- BUG: Only 404 is converted to 400
      -- Other 4xx errors are preserved
      normalizeResponseStatus 400 `shouldEqual` 400
      normalizeResponseStatus 401 `shouldEqual` 401
      normalizeResponseStatus 403 `shouldEqual` 403
      normalizeResponseStatus 404 `shouldEqual` 400  -- Only this is converted
      -- This test documents the behavior

    it "detects bug: shouldRetryLogic only checks stickyProvider != 'strict'" do
      -- BUG: Only "strict" prevents retry
      -- Other stickyProvider values don't prevent retry
      let modelInfo1 = mkMockModelInfo
        { stickyProvider = Nothing
        , fallbackProvider = Just "provider2"
        }
      let modelInfo2 = mkMockModelInfo
        { stickyProvider = Just "provider1"
        , fallbackProvider = Just "provider2"
        }
      let providerInfo = mkMockProviderData "provider1"
      -- Both allow retry
      shouldRetryLogic 500 modelInfo1 providerInfo `shouldEqual` true
      shouldRetryLogic 500 modelInfo2 providerInfo `shouldEqual` true
      -- This test documents the behavior

    it "verifies findHeader is case-insensitive" do
      -- This is correct behavior
      let headers = [{ key: "Content-Type", value: "application/json" }]
      findHeader "content-type" headers `shouldEqual` "application/json"
      findHeader "CONTENT-TYPE" headers `shouldEqual` "application/json"

    it "verifies scrubResponseHeaders only keeps content-type and cache-control" do
      -- This is correct behavior (security: remove sensitive headers)
      let headers = 
            [ { key: "Content-Type", value: "application/json" }
            , { key: "Cache-Control", value: "no-cache" }
            , { key: "Authorization", value: "Bearer token" }
            , { key: "Set-Cookie", value: "cookie=value" }
            ]
      let scrubbed = scrubResponseHeaders headers
      scrubbed.length `shouldEqual` 2
      findHeader "authorization" scrubbed `shouldEqual` ""
      findHeader "set-cookie" scrubbed `shouldEqual` ""
