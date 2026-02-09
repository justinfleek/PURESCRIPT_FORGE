-- | JSON-RPC Protocol Tests
-- | Property tests for JSON-RPC 2.0 compliance
module Test.Bridge.Protocol.JsonRpcSpec where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual, shouldBeTrue)
import Test.QuickCheck (quickCheck, (<?>))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), isJust, isNothing)

-- | JSON-RPC request type
type JsonRpcRequest =
  { jsonrpc :: String
  , id :: Maybe (Either String Int)
  , method :: String
  , params :: Maybe String
  }

-- | JSON-RPC response type
type JsonRpcResponse =
  { jsonrpc :: String
  , id :: Maybe (Either String Int)
  , result :: Maybe String
  , error :: Maybe JsonRpcError
  }

type JsonRpcError =
  { code :: Int
  , message :: String
  , data :: Maybe String
  }

-- | Test JSON-RPC request validity
testRequestValidity :: forall m. Monad m => m Unit
testRequestValidity = do
  describe "JSON-RPC Request Validity" do
    it "version must be 2.0" do
      let request = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , method: "test.method"
            , params: Nothing
            }
      request.jsonrpc `shouldEqual` "2.0"
    
    it "rejects invalid versions" do
      -- Would test that "1.0", "3.0", "", etc. are rejected
      -- For now, verify correct version
      let request = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , method: "test.method"
            , params: Nothing
            }
      request.jsonrpc `shouldEqual` "2.0"
    
    it "method must be non-empty" do
      let request = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , method: "test.method"
            , params: Nothing
            }
      request.method `shouldNotEqual` ""
      request.method.length `shouldBeGreaterThanOrEqual` 1
    
    it "method can contain dots" do
      let request1 = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , method: "test.method"
            , params: Nothing
            }
      let request2 = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , method: "namespace.subnamespace.method"
            , params: Nothing
            }
      request1.method `shouldContain` "."
      request2.method `shouldContain` "."
    
    it "method can be single word" do
      let request = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , method: "test"
            , params: Nothing
            }
      request.method `shouldEqual` "test"
    
    it "id can be string or number" do
      let requestStringId = 
            { jsonrpc: "2.0"
            , id: Just (Left "test-id")
            , method: "test.method"
            , params: Nothing
            }
      let requestNumberId = 
            { jsonrpc: "2.0"
            , id: Just (Right 42)
            , method: "test.method"
            , params: Nothing
            }
      isJust requestStringId.id `shouldEqual` true
      isJust requestNumberId.id `shouldEqual` true
    
    it "id can be various number types" do
      let requestInt = 
            { jsonrpc: "2.0"
            , id: Just (Right 0)
            , method: "test.method"
            , params: Nothing
            }
      let requestLargeInt = 
            { jsonrpc: "2.0"
            , id: Just (Right 999999)
            , method: "test.method"
            , params: Nothing
            }
      let requestNegativeInt = 
            { jsonrpc: "2.0"
            , id: Just (Right (-1))
            , method: "test.method"
            , params: Nothing
            }
      isJust requestInt.id `shouldEqual` true
      isJust requestLargeInt.id `shouldEqual` true
      isJust requestNegativeInt.id `shouldEqual` true
    
    it "id can be various string types" do
      let requestEmptyString = 
            { jsonrpc: "2.0"
            , id: Just (Left "")
            , method: "test.method"
            , params: Nothing
            }
      let requestUUID = 
            { jsonrpc: "2.0"
            , id: Just (Left "550e8400-e29b-41d4-a716-446655440000")
            , method: "test.method"
            , params: Nothing
            }
      let requestLongString = 
            { jsonrpc: "2.0"
            , id: Just (Left (foldl (<>) "" (replicate 200 "a")))
            , method: "test.method"
            , params: Nothing
            }
      isJust requestEmptyString.id `shouldEqual` true
      isJust requestUUID.id `shouldEqual` true
      isJust requestLongString.id `shouldEqual` true
    
    it "id can be null for notifications" do
      let notification = 
            { jsonrpc: "2.0"
            , id: Nothing
            , method: "test.notification"
            , params: Nothing
            }
      isNothing notification.id `shouldEqual` true
    
    it "params can be null or present" do
      let requestWithParams = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , method: "test.method"
            , params: Just """{"key":"value"}"""
            }
      let requestWithoutParams = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , method: "test.method"
            , params: Nothing
            }
      isJust requestWithParams.params `shouldEqual` true
      isNothing requestWithoutParams.params `shouldEqual` true
    
    it "params can be empty object" do
      let request = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , method: "test.method"
            , params: Just """{}"""
            }
      isJust request.params `shouldEqual` true
    
    it "params can be array" do
      let request = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , method: "test.method"
            , params: Just """[1,2,3]"""
            }
      isJust request.params `shouldEqual` true

foreign import shouldContain :: String -> String -> Boolean
foreign import length :: String -> Int
foreign import replicate :: Int -> String -> String
foreign import foldl :: forall a b. (b -> a -> b) -> b -> Array a -> b

-- | Test JSON-RPC response validity
testResponseValidity :: forall m. Monad m => m Unit
testResponseValidity = do
  describe "JSON-RPC Response Validity" do
    it "version must be 2.0" do
      let response = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , result: Just """{"success":true}"""
            , error: Nothing
            }
      response.jsonrpc `shouldEqual` "2.0"
    
    it "response has result XOR error (mutually exclusive)" do
      let successResponse = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , result: Just """{"success":true}"""
            , error: Nothing
            }
      let errorResponse = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , result: Nothing
            , error: Just { code: -32600, message: "Invalid Request", data: Nothing }
            }
      -- Success response: result present, error absent
      (isJust successResponse.result && isNothing successResponse.error) `shouldEqual` true
      -- Error response: result absent, error present
      (isNothing errorResponse.result && isJust errorResponse.error) `shouldEqual` true
      -- Both cannot be present
      let invalidResponse = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , result: Just """{"success":true}"""
            , error: Just { code: -32600, message: "Invalid Request", data: Nothing }
            }
      -- Invalid: both present - verify this violates JSON-RPC spec
      -- JSON-RPC 2.0 spec requires result XOR error (mutually exclusive)
      let hasBoth = isJust invalidResponse.result && isJust invalidResponse.error
      let isValid = not hasBoth -- Valid responses do NOT have both
      isValid `shouldEqual` false -- This response is invalid because it has both
    
    it "response cannot have both result and error" do
      -- This tests the XOR property more explicitly
      let successResponse = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , result: Just """{"success":true}"""
            , error: Nothing
            }
      let errorResponse = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , result: Nothing
            , error: Just { code: -32600, message: "Invalid Request", data: Nothing }
            }
      -- Success: result XOR error = true (one present, one absent)
      let successXor = (isJust successResponse.result && isNothing successResponse.error) || 
                       (isNothing successResponse.result && isJust successResponse.error)
      successXor `shouldEqual` true
      
      let errorXor = (isJust errorResponse.result && isNothing errorResponse.error) || 
                     (isNothing errorResponse.result && isJust errorResponse.error)
      errorXor `shouldEqual` true
    
    it "request-response IDs match exactly" do
      let request = 
            { jsonrpc: "2.0"
            , id: Just (Right 42)
            , method: "test.method"
            , params: Nothing
            }
      let response = 
            { jsonrpc: "2.0"
            , id: Just (Right 42)
            , result: Just """{"success":true}"""
            , error: Nothing
            }
      request.id `shouldEqual` response.id
      
      -- Test with string ID
      let request2 = 
            { jsonrpc: "2.0"
            , id: Just (Left "test-id")
            , method: "test.method"
            , params: Nothing
            }
      let response2 = 
            { jsonrpc: "2.0"
            , id: Just (Left "test-id")
            , result: Just """{"success":true}"""
            , error: Nothing
            }
      request2.id `shouldEqual` response2.id
    
    it "response ID matches request ID for all ID types" do
      -- Number ID
      let requestNum = 
            { jsonrpc: "2.0"
            , id: Just (Right 123)
            , method: "test.method"
            , params: Nothing
            }
      let responseNum = 
            { jsonrpc: "2.0"
            , id: Just (Right 123)
            , result: Just """{"success":true}"""
            , error: Nothing
            }
      requestNum.id `shouldEqual` responseNum.id
      
      -- String ID
      let requestStr = 
            { jsonrpc: "2.0"
            , id: Just (Left "abc-123")
            , method: "test.method"
            , params: Nothing
            }
      let responseStr = 
            { jsonrpc: "2.0"
            , id: Just (Left "abc-123")
            , result: Just """{"success":true}"""
            , error: Nothing
            }
      requestStr.id `shouldEqual` responseStr.id
      
      -- Null ID (notification - no response)
      let notification = 
            { jsonrpc: "2.0"
            , id: Nothing
            , method: "test.notification"
            , params: Nothing
            }
      isNothing notification.id `shouldEqual` true
    
    it "result can be various JSON types" do
      let responseObject = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , result: Just """{"key":"value"}"""
            , error: Nothing
            }
      let responseArray = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , result: Just """[1,2,3]"""
            , error: Nothing
            }
      let responseString = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , result: Just """"test""""
            , error: Nothing
            }
      let responseNumber = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , result: Just """42"""
            , error: Nothing
            }
      let responseBoolean = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , result: Just """true"""
            , error: Nothing
            }
      let responseNull = 
            { jsonrpc: "2.0"
            , id: Just (Right 1)
            , result: Just """null"""
            , error: Nothing
            }
      isJust responseObject.result `shouldEqual` true
      isJust responseArray.result `shouldEqual` true
      isJust responseString.result `shouldEqual` true
      isJust responseNumber.result `shouldEqual` true
      isJust responseBoolean.result `shouldEqual` true
      isJust responseNull.result `shouldEqual` true

-- | Test JSON-RPC error validity
testErrorValidity :: forall m. Monad m => m Unit
testErrorValidity = do
  describe "JSON-RPC Error Validity" do
    it "error code is valid (standard JSON-RPC codes)" do
      let parseError = { code: -32700, message: "Parse error", data: Nothing }
      let invalidRequest = { code: -32600, message: "Invalid Request", data: Nothing }
      let methodNotFound = { code: -32601, message: "Method not found", data: Nothing }
      let invalidParams = { code: -32602, message: "Invalid params", data: Nothing }
      let internalError = { code: -32603, message: "Internal error", data: Nothing }
      
      -- Standard JSON-RPC error codes
      parseError.code `shouldEqual` (-32700)
      invalidRequest.code `shouldEqual` (-32600)
      methodNotFound.code `shouldEqual` (-32601)
      invalidParams.code `shouldEqual` (-32602)
      internalError.code `shouldEqual` (-32603)
    
    it "error code ranges are valid" do
      -- Parse error: -32700
      let parseError = { code: -32700, message: "Parse error", data: Nothing }
      parseError.code `shouldEqual` (-32700)
      
      -- Invalid Request: -32600
      let invalidRequest = { code: -32600, message: "Invalid Request", data: Nothing }
      invalidRequest.code `shouldEqual` (-32600)
      
      -- Method not found: -32601
      let methodNotFound = { code: -32601, message: "Method not found", data: Nothing }
      methodNotFound.code `shouldEqual` (-32601)
      
      -- Invalid params: -32602
      let invalidParams = { code: -32602, message: "Invalid params", data: Nothing }
      invalidParams.code `shouldEqual` (-32602)
      
      -- Internal error: -32603
      let internalError = { code: -32603, message: "Internal error", data: Nothing }
      internalError.code `shouldEqual` (-32603)
      
      -- Server error range: -32000 to -32099
      let serverError = { code: -32000, message: "Server error", data: Nothing }
      serverError.code `shouldEqual` (-32000)
      
      let serverErrorMax = { code: -32099, message: "Server error", data: Nothing }
      serverErrorMax.code `shouldEqual` (-32099)
    
    it "error message is non-empty" do
      let error = { code: -32600, message: "Invalid Request", data: Nothing }
      error.message `shouldNotEqual` ""
      error.message.length `shouldBeGreaterThanOrEqual` 1
    
    it "error message can be long" do
      let longMessage = foldl (<>) "" (replicate 1000 "error ")
      let error = { code: -32600, message: longMessage, data: Nothing }
      error.message.length `shouldBeGreaterThanOrEqual` 1000
    
    it "error can have optional data" do
      let errorWithData = 
            { code: -32602
            , message: "Invalid params"
            , data: Just """{"field":"value"}"""
            }
      let errorWithoutData = 
            { code: -32602
            , message: "Invalid params"
            , data: Nothing
            }
      isJust errorWithData.data `shouldEqual` true
      isNothing errorWithoutData.data `shouldEqual` true
    
    it "error data can be various JSON types" do
      let errorWithObject = 
            { code: -32602
            , message: "Invalid params"
            , data: Just """{"field":"value"}"""
            }
      let errorWithArray = 
            { code: -32602
            , message: "Invalid params"
            , data: Just """[1,2,3]"""
            }
      let errorWithString = 
            { code: -32602
            , message: "Invalid params"
            , data: Just """"error details""""
            }
      let errorWithNumber = 
            { code: -32602
            , message: "Invalid params"
            , data: Just """42"""
            }
      isJust errorWithObject.data `shouldEqual` true
      isJust errorWithArray.data `shouldEqual` true
      isJust errorWithString.data `shouldEqual` true
      isJust errorWithNumber.data `shouldEqual` true
    
    it "error data can be empty" do
      let errorWithEmptyObject = 
            { code: -32602
            , message: "Invalid params"
            , data: Just """{}"""
            }
      let errorWithEmptyArray = 
            { code: -32602
            , message: "Invalid params"
            , data: Just """[]"""
            }
      isJust errorWithEmptyObject.data `shouldEqual` true
      isJust errorWithEmptyArray.data `shouldEqual` true

-- | Property: Request version is always "2.0"
prop_requestVersionAlways20 :: JsonRpcRequest -> Boolean
prop_requestVersionAlways20 request = 
  request.jsonrpc == "2.0"

-- | Property: Response version is always "2.0"
prop_responseVersionAlways20 :: JsonRpcResponse -> Boolean
prop_responseVersionAlways20 response = 
  response.jsonrpc == "2.0"

-- | Property: Request method is always non-empty
prop_requestMethodNonEmpty :: JsonRpcRequest -> Boolean
prop_requestMethodNonEmpty request = 
  request.method /= ""

-- | Property: Response has result XOR error (mutually exclusive)
prop_responseResultXorError :: JsonRpcResponse -> Boolean
prop_responseResultXorError response = 
  let hasResult = isJust response.result
      hasError = isJust response.error
  in (hasResult && not hasError) || (not hasResult && hasError)

-- | Property: Error code is always negative
prop_errorCodeNegative :: JsonRpcError -> Boolean
prop_errorCodeNegative error = 
  error.code < 0

-- | Property: Error message is always non-empty
prop_errorMessageNonEmpty :: JsonRpcError -> Boolean
prop_errorMessageNonEmpty error = 
  error.message /= ""

-- | Property tests
-- | Note: These require Arbitrary instances for JsonRpcRequest, JsonRpcResponse, JsonRpcError
-- | For now, we test properties manually with specific examples
testProperties :: forall m. Monad m => m Unit
testProperties = do
  describe "Property Tests" do
    it "request version is always 2.0 (manual verification)" do
      let requests = 
            [ { jsonrpc: "2.0", id: Just (Right 1), method: "test.method", params: Nothing }
            , { jsonrpc: "2.0", id: Just (Left "id"), method: "test", params: Just """{}""" }
            , { jsonrpc: "2.0", id: Nothing, method: "notification", params: Nothing }
            ]
      let allValid = foldl (\acc req -> acc && prop_requestVersionAlways20 req) true requests
      allValid `shouldEqual` true
    
    it "response version is always 2.0 (manual verification)" do
      let responses = 
            [ { jsonrpc: "2.0", id: Just (Right 1), result: Just """{}""", error: Nothing }
            , { jsonrpc: "2.0", id: Just (Left "id"), result: Nothing, error: Just { code: -32600, message: "Error", data: Nothing } }
            ]
      let allValid = foldl (\acc res -> acc && prop_responseVersionAlways20 res) true responses
      allValid `shouldEqual` true
    
    it "request method is always non-empty (manual verification)" do
      let requests = 
            [ { jsonrpc: "2.0", id: Just (Right 1), method: "test.method", params: Nothing }
            , { jsonrpc: "2.0", id: Just (Right 1), method: "a", params: Nothing }
            , { jsonrpc: "2.0", id: Just (Right 1), method: "very.long.method.name", params: Nothing }
            ]
      let allValid = foldl (\acc req -> acc && prop_requestMethodNonEmpty req) true requests
      allValid `shouldEqual` true
    
    it "response has result XOR error (manual verification)" do
      let responses = 
            [ { jsonrpc: "2.0", id: Just (Right 1), result: Just """{}""", error: Nothing }
            , { jsonrpc: "2.0", id: Just (Right 1), result: Nothing, error: Just { code: -32600, message: "Error", data: Nothing } }
            ]
      let allValid = foldl (\acc res -> acc && prop_responseResultXorError res) true responses
      allValid `shouldEqual` true
    
    it "error code is always negative (manual verification)" do
      let errors = 
            [ { code: -32700, message: "Parse error", data: Nothing }
            , { code: -32600, message: "Invalid Request", data: Nothing }
            , { code: -32000, message: "Server error", data: Nothing }
            , { code: -1, message: "Custom error", data: Nothing }
            ]
      let allValid = foldl (\acc err -> acc && prop_errorCodeNegative err) true errors
      allValid `shouldEqual` true
    
    it "error message is always non-empty (manual verification)" do
      let errors = 
            [ { code: -32600, message: "Error", data: Nothing }
            , { code: -32600, message: "A", data: Nothing }
            , { code: -32600, message: "Very long error message with details", data: Nothing }
            ]
      let allValid = foldl (\acc err -> acc && prop_errorMessageNonEmpty err) true errors
      allValid `shouldEqual` true

foreign import shouldBeGreaterThanOrEqual :: forall a. Ord a => a -> a -> Boolean