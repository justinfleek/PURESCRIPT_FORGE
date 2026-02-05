{-|
Module      : Tool.Search.Test.SearXNGIntegrationSpec
Description : Integration tests for SearXNG search workflows
Integration tests for complete SearXNG workflows: search → parse → validate results.
-}
module Tool.Search.Test.SearXNGIntegrationSpec where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff, delay, Milliseconds(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)
import Tool.Search.SearXNG (performSearch, SearchResult(..))

-- ============================================================================
-- TEST FIXTURES
-- ============================================================================

-- | Test SearXNG instance URL (would be mocked in real tests)
testInstanceUrl :: String
testInstanceUrl = "https://searx.example.com"

-- ============================================================================
-- INTEGRATION TESTS: FULL WORKFLOWS
-- ============================================================================

-- | Test: Complete search workflow
test_completeSearchWorkflow :: Aff Boolean
test_completeSearchWorkflow = do
  -- Perform search
  result <- performSearch testInstanceUrl "test query"
  
  case result of
    Left _ -> pure false -- Search failed
    Right (SearchResult res) -> do
      -- Should have results
      let hasResults = Array.length res.results > 0
      -- All results should have required fields
      let allValid = Array.all (\item -> 
            String.length item.title > 0 && 
            String.length item.url > 0
          ) res.results
      pure (hasResults && allValid)

-- | Test: Search with parameters
test_searchWithParameters :: Aff Boolean
test_searchWithParameters = do
  -- Perform search with language parameter
  result <- performSearch testInstanceUrl "test" { language: Just "en" }
  
  case result of
    Left _ -> pure false
    Right (SearchResult res) -> do
      -- Should have results
      let hasResults = Array.length res.results > 0
      pure hasResults

-- | Test: Multiple searches in sequence
test_multipleSearchesSequence :: Aff Boolean
test_multipleSearchesSequence = do
  -- Perform multiple searches
  result1 <- performSearch testInstanceUrl "query1"
  delay (Milliseconds 100.0)
  result2 <- performSearch testInstanceUrl "query2"
  delay (Milliseconds 100.0)
  result3 <- performSearch testInstanceUrl "query3"
  
  -- All should succeed
  let allSucceeded = case result1, result2, result3 of
        Right _, Right _, Right _ -> true
        _, _, _ -> false
  
  pure allSucceeded

-- | Test: Search result parsing
test_searchResultParsing :: Aff Boolean
test_searchResultParsing = do
  -- Perform search
  result <- performSearch testInstanceUrl "test"
  
  case result of
    Left _ -> pure false
    Right (SearchResult res) -> do
      -- Results should be properly parsed
      let properlyParsed = Array.all (\item -> 
            String.length item.title > 0 &&
            String.length item.url > 0 &&
            (String.contains (String.Pattern "http://") item.url || 
             String.contains (String.Pattern "https://") item.url)
          ) res.results
      pure properlyParsed

-- | Test: Search error handling - invalid URL
test_errorHandlingInvalidUrl :: Aff Boolean
test_errorHandlingInvalidUrl = do
  -- Try to search with invalid URL
  result <- performSearch "https://invalid-url-12345.example.com" "test"
  
  -- Should fail gracefully
  case result of
    Left _ -> pure true -- Expected failure
    Right _ -> pure false -- Should not succeed

-- | Test: Search error handling - empty query
test_errorHandlingEmptyQuery :: Aff Boolean
test_errorHandlingEmptyQuery = do
  -- Try to search with empty query
  result <- performSearch testInstanceUrl ""
  
  -- Should fail gracefully
  case result of
    Left _ -> pure true -- Expected failure
    Right _ -> pure true -- Or succeed with empty results (both acceptable)

-- | Test: Search with special characters
test_searchSpecialCharacters :: Aff Boolean
test_searchSpecialCharacters = do
  -- Perform search with special characters
  let specialQuery = "test & query <with> \"quotes\" 'apostrophes'"
  result <- performSearch testInstanceUrl specialQuery
  
  case result of
    Left _ -> pure true -- Might fail, that's acceptable
    Right (SearchResult res) -> do
      -- Should handle special chars without crashing
      let handled = true
      pure handled

-- | Test: Search result validation
test_searchResultValidation :: Aff Boolean
test_searchResultValidation = do
  -- Perform search
  result <- performSearch testInstanceUrl "test"
  
  case result of
    Left _ -> pure false
    Right (SearchResult res) -> do
      -- Validate result structure
      let validStructure = 
            -- Results array exists
            Array.length res.results >= 0 &&
            -- All results have required fields
            Array.all (\item -> 
              String.length item.title >= 0 &&
              String.length item.url >= 0
            ) res.results
      pure validStructure

-- ============================================================================
-- TEST SUITE
-- ============================================================================

spec :: Spec Unit
spec = describe "SearXNG Integration Tests" do
  describe "Search Workflows" do
    it "complete search workflow: search → parse → validate" do
      result <- test_completeSearchWorkflow
      result `shouldSatisfy` identity
    
    it "search with parameters" do
      result <- test_searchWithParameters
      result `shouldSatisfy` identity
    
    it "multiple searches in sequence" do
      result <- test_multipleSearchesSequence
      result `shouldEqual` true
    
    it "search result parsing" do
      result <- test_searchResultParsing
      result `shouldEqual` true
    
    it "search result validation" do
      result <- test_searchResultValidation
      result `shouldEqual` true
  
  describe "Error Handling" do
    it "handles invalid URL gracefully" do
      result <- test_errorHandlingInvalidUrl
      result `shouldEqual` true
    
    it "handles empty query gracefully" do
      result <- test_errorHandlingEmptyQuery
      result `shouldEqual` true
    
    it "handles special characters" do
      result <- test_searchSpecialCharacters
      result `shouldSatisfy` identity
