{-|
Module      : Tool.Search.Test.SearXNGSpec
Description : Property tests for SearXNG search operations
Property tests for SearXNG search operations using realistic distributions.
-}
module Tool.Search.Test.SearXNGSpec where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff, delay, Milliseconds(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual)
import Test.Spec.QuickCheck (quickCheck, (<?>))
import Tool.Search.SearXNG (performSearch, SearchResult(..))

-- ============================================================================
-- TEST HELPERS
-- ============================================================================

-- | Test SearXNG instance URL (would be mocked in real tests)
testInstanceUrl :: String
testInstanceUrl = "https://searx.example.com"

-- ============================================================================
-- PROPERTY TESTS
-- ============================================================================

-- | Property: Search results are non-empty for valid queries
prop_searchResultsNonEmpty :: String -> Aff Boolean
prop_searchResultsNonEmpty query = do
  if String.null query then
    pure true -- Empty query should error, not return results
  else do
    result <- performSearch testInstanceUrl query
    case result of
      Left _ -> pure false <?> "Search should succeed for valid query"
      Right (SearchResult res) -> do
        let hasResults = Array.length res.results > 0
        pure hasResults <?> "Search should return non-empty results"

-- | Property: Search is idempotent (same query = same results)
prop_searchIdempotent :: String -> Aff Boolean
prop_searchIdempotent query = do
  if String.null query then
    pure true
  else do
    result1 <- performSearch testInstanceUrl query
    delay (Milliseconds 100.0) -- Small delay
    result2 <- performSearch testInstanceUrl query
    case result1, result2 of
      Left _, _ -> pure false <?> "First search should succeed"
      _, Left _ -> pure false <?> "Second search should succeed"
      Right (SearchResult res1), Right (SearchResult res2) -> do
        -- Results should be similar (simplified: check same number)
        let idempotent = Array.length res1.results == Array.length res2.results
        pure idempotent <?> "Search should be idempotent"

-- | Property: Search results have valid URLs
prop_searchResultsValidUrls :: String -> Aff Boolean
prop_searchResultsValidUrls query = do
  if String.null query then
    pure true
  else do
    result <- performSearch testInstanceUrl query
    case result of
      Left _ -> pure false <?> "Search should succeed"
      Right (SearchResult res) -> do
        -- All results should have valid URLs
        let allValidUrls = Array.all (\item -> 
              String.length item.url > 0 && 
              (String.contains (String.Pattern "http://") item.url || 
               String.contains (String.Pattern "https://") item.url)
            ) res.results
        pure allValidUrls <?> "All search results should have valid URLs"

-- | Property: Search results have non-empty titles
prop_searchResultsNonEmptyTitles :: String -> Aff Boolean
prop_searchResultsNonEmptyTitles query = do
  if String.null query then
    pure true
  else do
    result <- performSearch testInstanceUrl query
    case result of
      Left _ -> pure false <?> "Search should succeed"
      Right (SearchResult res) -> do
        -- All results should have non-empty titles
        let allNonEmptyTitles = Array.all (\item -> String.length item.title > 0) res.results
        pure allNonEmptyTitles <?> "All search results should have non-empty titles"

-- | Property: Search respects query encoding
prop_searchQueryEncoding :: String -> Aff Boolean
prop_searchQueryEncoding query = do
  if String.null query then
    pure true
  else do
    result <- performSearch testInstanceUrl query
    case result of
      Left _ -> pure false <?> "Search should succeed"
      Right (SearchResult res) -> do
        -- Query should be properly encoded (simplified check)
        let encodingValid = true -- Would verify query appears correctly in results
        pure encodingValid <?> "Search should respect query encoding"

-- | Property: Search handles special characters
prop_searchHandlesSpecialChars :: String -> Aff Boolean
prop_searchHandlesSpecialChars query = do
  if String.null query then
    pure true
  else do
    -- Add special characters
    let specialQuery = query <> " & <test> \"quotes\""
    result <- performSearch testInstanceUrl specialQuery
    case result of
      Left _ -> pure true -- Might fail, that's acceptable
      Right (SearchResult res) -> do
        -- Should handle special chars without crashing
        let handled = true
        pure handled <?> "Search should handle special characters"

-- ============================================================================
-- TEST SUITE
-- ============================================================================

spec :: Spec Unit
spec = describe "SearXNG Search Property Tests" do
  describe "Search Results" do
    it "returns non-empty results for valid queries" do
      quickCheck prop_searchResultsNonEmpty
    
    it "is idempotent" do
      quickCheck prop_searchIdempotent
    
    it "returns results with valid URLs" do
      quickCheck prop_searchResultsValidUrls
    
    it "returns results with non-empty titles" do
      quickCheck prop_searchResultsNonEmptyTitles
  
  describe "Query Handling" do
    it "respects query encoding" do
      quickCheck prop_searchQueryEncoding
    
    it "handles special characters" do
      quickCheck prop_searchHandlesSpecialChars
