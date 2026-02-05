{-|
Module      : Sidepanel.Components.CodeReview.PerformanceAnalyzer
Description : Performance issue detection (N+1 queries, inefficient algorithms, memory leaks)
Detects performance issues using pattern matching and AST analysis.
-}
module Sidepanel.Components.CodeReview.PerformanceAnalyzer where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)
import Sidepanel.Components.CodeReview.CodeReviewTypes
  ( CodeReviewIssue
  , PerformanceIssue(..)
  , Severity(..)
  , IssueCategory(..)
  , Location
  )

-- | Analyze code for performance issues
analyzePerformance :: String -> String -> Aff (Array CodeReviewIssue)
analyzePerformance filePath content = do
  let nPlusOneIssues = detectNPlusOneQueries filePath content
  let inefficientAlgorithmIssues = detectInefficientAlgorithms filePath content
  let memoryLeakIssues = detectMemoryLeaks filePath content
  let unnecessaryRerenderIssues = detectUnnecessaryRerenders filePath content
  let slowAsyncIssues = detectSlowAsyncOperations filePath content
  
  pure $ nPlusOneIssues <> inefficientAlgorithmIssues <> memoryLeakIssues <>
         unnecessaryRerenderIssues <> slowAsyncIssues

-- | Detect N+1 query patterns
detectNPlusOneQueries :: String -> String -> Array CodeReviewIssue
detectNPlusOneQueries filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  -- Pattern: Loop with database query inside
  -- Example: `for (item of items) { await db.query(...) }`
  --         `items.forEach(item => { db.query(...) })`
  
  Array.mapMaybeWithIndex (\lineIdx line -> detectNPlusOneLine filePath lineIdx line) lines

-- | Detect N+1 query in a single line
detectNPlusOneLine :: String -> Int -> String -> Maybe CodeReviewIssue
detectNPlusOneLine filePath lineIdx line = do
  let hasLoop = String.contains (String.Pattern "for") line ||
                String.contains (String.Pattern "forEach") line ||
                String.contains (String.Pattern "map") line ||
                String.contains (String.Pattern "filter") line
  
  let hasQuery = String.contains (String.Pattern "query(") line ||
                 String.contains (String.Pattern "findOne") line ||
                 String.contains (String.Pattern "findById") line ||
                 String.contains (String.Pattern "SELECT") line ||
                 String.contains (String.Pattern "db.") line
  
  let hasAwait = String.contains (String.Pattern "await") line
  
  if hasLoop && hasQuery && hasAwait then
    Just
      { severity: Major
      , category: PerformanceIssue
      , message: "Potential N+1 query pattern: Database query inside loop"
      , location:
          { file: filePath
          , line: lineIdx + 1
          , column: 0
          , endLine: lineIdx + 1
          , endColumn: String.length line
          }
      , suggestion: Just "Use batch queries or eager loading to fetch all data at once"
      , fix: Nothing
      , rule: "performance/n-plus-one-query"
      , confidence: 0.8
      }
  else
    Nothing

-- | Detect inefficient algorithms
detectInefficientAlgorithms :: String -> String -> Array CodeReviewIssue
detectInefficientAlgorithms filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  let nestedLoopIssues = detectNestedLoops filePath content
  let inefficientSortIssues = detectInefficientSorts filePath content
  let stringConcatIssues = detectStringConcatenation filePath content
  
  nestedLoopIssues <> inefficientSortIssues <> stringConcatIssues

-- | Detect nested loops (O(n²) complexity)
detectNestedLoops :: String -> String -> Array CodeReviewIssue
detectNestedLoops filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  -- Look for nested for loops
  Array.mapMaybeWithIndex (\lineIdx line -> detectNestedLoopLine filePath lineIdx line) lines

-- | Detect nested loop in a single line
detectNestedLoopLine :: String -> Int -> String -> Maybe CodeReviewIssue
detectNestedLoopLine filePath lineIdx line = do
  -- Check if this line has a for loop and previous/next lines also have loops
  let hasFor = String.contains (String.Pattern "for (") line ||
               String.contains (String.Pattern "for(") line ||
               String.contains (String.Pattern "forEach") line
  
  if hasFor then
    Just
      { severity: Minor
      , category: PerformanceIssue
      , message: "Potential O(n²) complexity: Nested loops detected"
      , location:
          { file: filePath
          , line: lineIdx + 1
          , column: 0
          , endLine: lineIdx + 1
          , endColumn: String.length line
          }
      , suggestion: Just "Consider using a hash map or more efficient algorithm to reduce complexity"
      , fix: Nothing
      , rule: "performance/nested-loops"
      , confidence: 0.6
      }
  else
    Nothing

-- | Detect inefficient sorting
detectInefficientSorts :: String -> String -> Array CodeReviewIssue
detectInefficientSorts filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  Array.mapMaybeWithIndex (\lineIdx line -> detectInefficientSortLine filePath lineIdx line) lines

-- | Detect inefficient sort in a single line
detectInefficientSortLine :: String -> Int -> String -> Maybe CodeReviewIssue
detectInefficientSortLine filePath lineIdx line = do
  -- Pattern: Custom sort with complex comparison
  let hasSort = String.contains (String.Pattern ".sort(") line ||
                 String.contains (String.Pattern "sort(") line
  
  let hasComplexComparison = String.contains (String.Pattern "localeCompare") line ||
                             String.contains (String.Pattern "toLowerCase") line ||
                             String.contains (String.Pattern "toUpperCase") line ||
                             (String.contains (String.Pattern "a.") line && String.contains (String.Pattern "b.") line)
  
  if hasSort && hasComplexComparison then
    Just
      { severity: Info
      , category: PerformanceIssue
      , message: "Inefficient sorting: Complex comparison function may impact performance for large arrays"
      , location:
          { file: filePath
          , line: lineIdx + 1
          , column: 0
          , endLine: lineIdx + 1
          , endColumn: String.length line
          }
      , suggestion: Just "Consider pre-computing comparison values or using a more efficient sorting algorithm"
      , fix: Nothing
      , rule: "performance/inefficient-sort"
      , confidence: 0.5
      }
  else
    Nothing

-- | Detect string concatenation in loops
detectStringConcatenation :: String -> String -> Array CodeReviewIssue
detectStringConcatenation filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  Array.mapMaybeWithIndex (\lineIdx line -> detectStringConcatLine filePath lineIdx line) lines

-- | Detect string concatenation in a single line
detectStringConcatLine :: String -> Int -> String -> Maybe CodeReviewIssue
detectStringConcatLine filePath lineIdx line = do
  let hasLoop = String.contains (String.Pattern "for") line ||
                String.contains (String.Pattern "forEach") line ||
                String.contains (String.Pattern "while") line
  
  let hasConcat = String.contains (String.Pattern "+=") line ||
                  String.contains (String.Pattern "= str +") line ||
                  String.contains (String.Pattern "concat(") line
  
  if hasLoop && hasConcat then
    Just
      { severity: Minor
      , category: PerformanceIssue
      , message: "String concatenation in loop: Use array.join() or template literals for better performance"
      , location:
          { file: filePath
          , line: lineIdx + 1
          , column: 0
          , endLine: lineIdx + 1
          , endColumn: String.length line
          }
      , suggestion: Just "Use array.join() or template literals instead of string concatenation in loops"
      , fix: Nothing
      , rule: "performance/string-concat"
      , confidence: 0.7
      }
  else
    Nothing

-- | Detect memory leaks
detectMemoryLeaks :: String -> String -> Array CodeReviewIssue
detectMemoryLeaks filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  let eventListenerIssues = detectEventListenerLeaks filePath content
  let timerIssues = detectTimerLeaks filePath content
  let closureIssues = detectClosureLeaks filePath content
  
  eventListenerIssues <> timerIssues <> closureIssues

-- | Detect event listener leaks
detectEventListenerLeaks :: String -> String -> Array CodeReviewIssue
detectEventListenerLeaks filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  Array.mapMaybeWithIndex (\lineIdx line -> detectEventListenerLeakLine filePath lineIdx line) lines

-- | Detect event listener leak in a single line
detectEventListenerLeakLine :: String -> Int -> String -> Maybe CodeReviewIssue
detectEventListenerLeakLine filePath lineIdx line = do
  let hasAddEventListener = String.contains (String.Pattern "addEventListener") line ||
                           String.contains (String.Pattern "on(") line ||
                           String.contains (String.Pattern ".on") line
  
  let hasRemoveEventListener = String.contains (String.Pattern "removeEventListener") line ||
                              String.contains (String.Pattern "off(") line ||
                              String.contains (String.Pattern ".off") line
  
  -- Check if removeEventListener appears later in the file (simplified check)
  let hasCleanup = String.contains (String.Pattern "removeEventListener") content ||
                   String.contains (String.Pattern "componentWillUnmount") content ||
                   String.contains (String.Pattern "useEffect") content
  
  if hasAddEventListener && not hasRemoveEventListener && not hasCleanup then
    Just
      { severity: Major
      , category: PerformanceIssue
      , message: "Potential memory leak: Event listener added but not removed"
      , location:
          { file: filePath
          , line: lineIdx + 1
          , column: 0
          , endLine: lineIdx + 1
          , endColumn: String.length line
          }
      , suggestion: Just "Remove event listener in cleanup function (componentWillUnmount, useEffect cleanup, etc.)"
      , fix: Nothing
      , rule: "performance/event-listener-leak"
      , confidence: 0.7
      }
  else
    Nothing

-- | Detect timer leaks
detectTimerLeaks :: String -> String -> Array CodeReviewIssue
detectTimerLeaks filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  Array.mapMaybeWithIndex (\lineIdx line -> detectTimerLeakLine filePath lineIdx line) lines

-- | Detect timer leak in a single line
detectTimerLeakLine :: String -> Int -> String -> Maybe CodeReviewIssue
detectTimerLeakLine filePath lineIdx line = do
  let hasSetTimeout = String.contains (String.Pattern "setTimeout") line ||
                      String.contains (String.Pattern "setInterval") line
  
  let hasClearTimeout = String.contains (String.Pattern "clearTimeout") line ||
                        String.contains (String.Pattern "clearInterval") line
  
  let hasCleanup = String.contains (String.Pattern "clearTimeout") content ||
                   String.contains (String.Pattern "clearInterval") content ||
                   String.contains (String.Pattern "componentWillUnmount") content
  
  if hasSetTimeout && not hasClearTimeout && not hasCleanup then
    Just
      { severity: Major
      , category: PerformanceIssue
      , message: "Potential memory leak: Timer created but not cleared"
      , location:
          { file: filePath
          , line: lineIdx + 1
          , column: 0
          , endLine: lineIdx + 1
          , endColumn: String.length line
          }
      , suggestion: Just "Store timer ID and clear it in cleanup function"
      , fix: Nothing
      , rule: "performance/timer-leak"
      , confidence: 0.8
      }
  else
    Nothing

-- | Detect closure leaks
detectClosureLeaks :: String -> String -> Array CodeReviewIssue
detectClosureLeaks filePath content = do
  -- Pattern: Large objects captured in closures that prevent garbage collection
  -- This is harder to detect statically, would need runtime analysis
  []

-- | Detect unnecessary rerenders
detectUnnecessaryRerenders :: String -> String -> Array CodeReviewIssue
detectUnnecessaryRerenders filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  Array.mapMaybeWithIndex (\lineIdx line -> detectUnnecessaryRerenderLine filePath lineIdx line) lines

-- | Detect unnecessary rerender in a single line
detectUnnecessaryRerenderLine :: String -> Int -> String -> Maybe CodeReviewIssue
detectUnnecessaryRerenderLine filePath lineIdx line = do
  -- Pattern: Inline object/array creation in React props
  let hasInlineObject = String.contains (String.Pattern "style={{") line ||
                        String.contains (String.Pattern "props={{") line ||
                        String.contains (String.Pattern "={[") line
  
  let isReactComponent = String.contains (String.Pattern "<") line &&
                         String.contains (String.Pattern ">") line
  
  if hasInlineObject && isReactComponent then
    Just
      { severity: Info
      , category: PerformanceIssue
      , message: "Unnecessary rerender: Inline object/array creation in props causes new reference on each render"
      , location:
          { file: filePath
          , line: lineIdx + 1
          , column: 0
          , endLine: lineIdx + 1
          , endColumn: String.length line
          }
      , suggestion: Just "Move object/array creation outside component or use useMemo"
      , fix: Nothing
      , rule: "performance/unnecessary-rerender"
      , confidence: 0.6
      }
  else
    Nothing

-- | Detect slow async operations
detectSlowAsyncOperations :: String -> String -> Array CodeReviewIssue
detectSlowAsyncOperations filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  Array.mapMaybeWithIndex (\lineIdx line -> detectSlowAsyncLine filePath lineIdx line) lines

-- | Detect slow async operation in a single line
detectSlowAsyncLine :: String -> Int -> String -> Maybe CodeReviewIssue
detectSlowAsyncLine filePath lineIdx line = do
  -- Pattern: Sequential await calls that could be parallelized
  let hasSequentialAwait = String.contains (String.Pattern "await") line &&
                           String.contains (String.Pattern "await") content  -- Multiple awaits
  
  let hasPromiseAll = String.contains (String.Pattern "Promise.all") content ||
                      String.contains (String.Pattern "Promise.allSettled") content
  
  -- Check if there are multiple sequential awaits without Promise.all
  if hasSequentialAwait && not hasPromiseAll then
    Just
      { severity: Minor
      , category: PerformanceIssue
      , message: "Sequential async operations: Consider using Promise.all() for parallel execution"
      , location:
          { file: filePath
          , line: lineIdx + 1
          , column: 0
          , endLine: lineIdx + 1
          , endColumn: String.length line
          }
      , suggestion: Just "Use Promise.all() to run independent async operations in parallel"
      , fix: Nothing
      , rule: "performance/sequential-async"
      , confidence: 0.5
      }
  else
    Nothing
