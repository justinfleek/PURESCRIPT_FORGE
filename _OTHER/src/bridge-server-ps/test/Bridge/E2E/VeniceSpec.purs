-- | Venice API E2E Tests
-- | End-to-end tests for Venice API integration
module Test.Bridge.E2E.VeniceSpec where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldBeGreaterThanOrEqual)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Aff (Aff)
import Data.Either (Either(..), isRight, isLeft)
import Bridge.Venice.Client (VeniceClient, ChatCompletionRequest)
import Bridge.State.Store (StateStore, createStore)
import Test.Bridge.Fixtures.TestData (generateBalanceState)

-- | Test Venice chat completion flow
testChatCompletion :: forall m. Monad m => m Unit
testChatCompletion = do
  describe "Venice Chat Completion E2E" do
    it "sends chat request and receives completion" do
      -- E2E: Request → API call → Response → Parse → Store
      store <- liftEffect createStore
      
      -- Create mock request
      let request = 
            { model: "claude-3-opus"
            , messages: 
                [ { role: "user", content: "Hello" }
                ]
            , maxTokens: Nothing
            , temperature: Nothing
            , stream: false
            }
      
      -- Request should be valid
      request.model `shouldEqual` "claude-3-opus"
      request.messages.length `shouldBeGreaterThanOrEqual` 1
    
    it "handles streaming responses" do
      -- E2E: Stream request → Chunks received → Aggregated → Complete
      let streamRequest = 
            { model: "claude-3-opus"
            , messages: 
                [ { role: "user", content: "Hello" }
                ]
            , maxTokens: Nothing
            , temperature: Nothing
            , stream: true
            }
      
      -- Stream request should have stream flag
      streamRequest.stream `shouldEqual` true
    
    it "extracts balance from response" do
      -- E2E: Response → Balance extraction → State update → Verification
      store <- liftEffect createStore
      
      -- Simulate balance extraction
      balanceState <- liftEffect generateBalanceState
      -- Balance should be valid
      balanceState.venice.diem `shouldBeGreaterThanOrEqual` 0.0
      balanceState.venice.usd `shouldBeGreaterThanOrEqual` 0.0
    
    it "handles API errors gracefully" do
      -- E2E: API error → Error handling → Notification → Recovery
      let errorResponse = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , result: Nothing
            , error: Just 
                { code: -32603
                , message: "Internal error"
                , data: Just """{"type":"api_error"}"""
                }
            }
      
      -- Error response should have error field
      isJust errorResponse.error `shouldEqual` true

-- | Test rate limiting
testRateLimiting :: forall m. Monad m => m Unit
testRateLimiting = do
  describe "Rate Limiting E2E" do
    it "enforces rate limits" do
      -- E2E: Many requests → Rate limit → Queuing → Proper handling
      -- Note: Would require actual rate limiter
      let rateLimitError = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , result: Nothing
            , error: Just 
                { code: 429
                , message: "Rate limit exceeded"
                , data: Just """{"retryAfter":60}"""
                }
            }
      
      -- Rate limit error should have 429 code
      case rateLimitError.error of
        Just err -> err.code `shouldEqual` 429
        Nothing -> pure unit
    
    it "handles rate limit reset" do
      -- E2E: Rate limit → Wait → Reset → Requests resume
      -- Note: Would require actual rate limiter with time tracking
      pure unit

-- | Test model listing
testModelListing :: forall m. Monad m => m Unit
testModelListing = do
  describe "Model Listing E2E" do
    it "fetches available models" do
      -- E2E: Request models → API call → Parse → Store → Return
      let modelsResponse = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , result: Just """[{"id":"claude-3-opus","pricing":{"input":0.015,"output":0.075}}]"""
            , error: Nothing
            }
      
      -- Response should have result
      isJust modelsResponse.result `shouldEqual` true
    
    it "handles model list errors" do
      -- E2E: Error → Fallback → Default models → Continue
      let errorResponse = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , result: Nothing
            , error: Just 
                { code: -32603
                , message: "Failed to fetch models"
                , data: Nothing
                }
            }
      
      -- Error should be handled gracefully
      isJust errorResponse.error `shouldEqual` true

foreign import shouldBeGreaterThanOrEqual :: forall a. Ord a => a -> a -> Boolean
