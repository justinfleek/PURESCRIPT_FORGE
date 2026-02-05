{-|
Module      : Sidepanel.Components.ErrorAnalysis.ErrorAnalyzer
Description : Core error analysis engine
Analyzes errors, explains them, finds root causes, and suggests fixes.
-}
module Sidepanel.Components.ErrorAnalysis.ErrorAnalyzer where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Effect.Aff (Aff)
import Sidepanel.Components.ErrorAnalysis.ErrorAnalysisTypes
  ( ErrorAnalysis
  , Error
  , ErrorType(..)
  , ErrorSeverity(..)
  , Location
  , FixSuggestion
  , CodeFix
  , CodeRange
  , ErrorPattern
  )

-- | Analyze error and provide comprehensive analysis
analyzeError :: Error -> Aff ErrorAnalysis
analyzeError error = do
  -- 1. Classify error type
  let errorType = classifyError error
  
  -- 2. Explain error
  let explanation = explainError error errorType
  
  -- 3. Find root cause
  let rootCause = findRootCause error
  
  -- 4. Generate fix suggestions
  let suggestions = generateFixSuggestions error errorType
  
  -- 5. Find related errors
  let relatedErrors = findRelatedErrors error
  
  -- 6. Generate debugging steps
  let debuggingSteps = generateDebuggingSteps error errorType
  
  -- 7. Determine severity
  let severity = determineSeverity error errorType
  
  pure
    { error: error
    , explanation: explanation
    , rootCause: rootCause
    , suggestions: suggestions
    , relatedErrors: relatedErrors
    , debuggingSteps: debuggingSteps
    , severity: severity
    }

-- | Classify error type from message and context
classifyError :: Error -> ErrorType
classifyError error =
  let msg = String.toLower error.message
      type_ = error.type_
  in
    -- Use explicit type if available
    if type_ /= CompileError then
      type_
    -- Otherwise infer from message patterns
    else if String.contains (String.Pattern "type") msg ||
            String.contains (String.Pattern "cannot convert") msg ||
            String.contains (String.Pattern "type mismatch") msg then
      TypeError
    else if String.contains (String.Pattern "syntax") msg ||
            String.contains (String.Pattern "parse") msg ||
            String.contains (String.Pattern "unexpected") msg then
      SyntaxError
    else if String.contains (String.Pattern "null") msg ||
            String.contains (String.Pattern "undefined") msg ||
            String.contains (String.Pattern "cannot read") msg then
      RuntimeError
    else if String.contains (String.Pattern "security") msg ||
            String.contains (String.Pattern "vulnerability") msg ||
            String.contains (String.Pattern "injection") msg then
      SecurityError
    else if String.contains (String.Pattern "test") msg ||
            String.contains (String.Pattern "assertion") msg ||
            String.contains (String.Pattern "expected") msg then
      TestFailure
    else
      CompileError

-- | Explain what the error means
explainError :: Error -> ErrorType -> String
explainError error errorType =
  let baseExplanation = case errorType of
        TypeError -> "Type error: The types of values don't match what's expected."
        SyntaxError -> "Syntax error: The code structure is invalid."
        RuntimeError -> "Runtime error: An error occurred while executing the code."
        LogicError -> "Logic error: The code runs but produces incorrect results."
        SecurityError -> "Security error: Potential security vulnerability detected."
        PerformanceError -> "Performance error: Code may be inefficient or slow."
        TestFailure -> "Test failure: A test assertion failed."
        CompileError -> "Compilation error: The code cannot be compiled."
      
      locationInfo = case error.location of
        Nothing -> ""
        Just loc -> " at " <> loc.file <> ":" <> show loc.line <> ":" <> show loc.column
      
      contextInfo = if String.length error.context.surroundingCode > 0 then
        " Context: " <> String.take 200 error.context.surroundingCode
      else
        ""
  in
    baseExplanation <> locationInfo <> contextInfo <> "\n\n" <> error.message

-- | Find root cause of error
findRootCause :: Error -> Maybe Location
findRootCause error =
  -- Start with error location
  case error.location of
    Nothing -> Nothing
    Just loc -> do
      -- Check stack trace for earlier location
      case error.stackTrace of
        Nothing -> Just loc
        Just trace -> do
          -- Find first frame with file location
          case Array.find (\f -> f.file /= Nothing) trace.frames of
            Nothing -> Just loc
            Just frame -> do
              file <- frame.file
              line <- frame.line
              column <- frame.column
              Just
                { file: file
                , line: fromMaybe 0 line
                , column: fromMaybe 0 column
                , endLine: Nothing
                , endColumn: Nothing
                }

-- | Generate fix suggestions
generateFixSuggestions :: Error -> ErrorType -> Array FixSuggestion
generateFixSuggestions error errorType =
  let patternSuggestions = matchErrorPatterns error errorType
      contextualSuggestions = generateContextualFixes error errorType
  in
    Array.take 5 (patternSuggestions <> contextualSuggestions)

-- | Match error against known patterns
matchErrorPatterns :: Error -> ErrorType -> Array FixSuggestion
matchErrorPatterns error errorType =
  let msg = String.toLower error.message
      patterns = getErrorPatterns errorType
      matches = Array.filter (\p -> String.contains (String.Pattern p.pattern) msg) patterns
  in
    Array.map (\p ->
      { description: p.typicalFix
      , fix: Nothing  -- Would generate actual fix
      , confidence: 0.7
      , explanation: p.commonCause
      }
    ) matches

-- | Generate contextual fixes based on error and code
generateContextualFixes :: Error -> ErrorType -> Array FixSuggestion
generateContextualFixes error errorType =
  case errorType of
    TypeError -> generateTypeErrorFixes error
    SyntaxError -> generateSyntaxErrorFixes error
    RuntimeError -> generateRuntimeErrorFixes error
    LogicError -> generateLogicErrorFixes error
    SecurityError -> generateSecurityErrorFixes error
    PerformanceError -> generatePerformanceErrorFixes error
    TestFailure -> generateTestFailureFixes error
    CompileError -> generateCompileErrorFixes error

-- | Generate fixes for type errors
generateTypeErrorFixes :: Error -> Array FixSuggestion
generateTypeErrorFixes error =
  [ { description: "Check type annotations match actual types"
    , fix: Nothing
    , confidence: 0.8
    , explanation: "Type errors often occur when declared types don't match usage."
    }
  , { description: "Verify imports are correct"
    , fix: Nothing
    , confidence: 0.6
    , explanation: "Missing or incorrect imports can cause type mismatches."
    }
  ]

-- | Generate fixes for syntax errors
generateSyntaxErrorFixes :: Error -> Array FixSuggestion
generateSyntaxErrorFixes error =
  [ { description: "Check for missing brackets, parentheses, or quotes"
    , fix: Nothing
    , confidence: 0.9
    , explanation: "Syntax errors are usually caused by mismatched delimiters."
    }
  ]

-- | Generate fixes for runtime errors
generateRuntimeErrorFixes :: Error -> Array FixSuggestion
generateRuntimeErrorFixes error =
  let msg = String.toLower error.message
  in
    if String.contains (String.Pattern "null") msg ||
       String.contains (String.Pattern "undefined") msg then
      [ { description: "Add null/undefined check before accessing value"
        , fix: Nothing
        , confidence: 0.9
        , explanation: "Null/undefined values need to be checked before use."
        }
      ]
    else
      [ { description: "Check variable initialization"
        , fix: Nothing
        , confidence: 0.7
        , explanation: "Runtime errors often occur when variables aren't initialized."
        }
      ]

-- | Generate fixes for logic errors
generateLogicErrorFixes :: Error -> Array FixSuggestion
generateLogicErrorFixes error =
  [ { description: "Review algorithm logic and edge cases"
    , fix: Nothing
    , confidence: 0.6
    , explanation: "Logic errors require careful review of the algorithm."
    }
  ]

-- | Generate fixes for security errors
generateSecurityErrorFixes :: Error -> Array FixSuggestion
generateSecurityErrorFixes error =
  [ { description: "Use parameterized queries instead of string concatenation"
    , fix: Nothing
    , confidence: 0.9
    , explanation: "SQL injection vulnerabilities require parameterized queries."
    }
  , { description: "Sanitize user input"
    , fix: Nothing
    , confidence: 0.8
    , explanation: "XSS vulnerabilities require input sanitization."
    }
  ]

-- | Generate fixes for performance errors
generatePerformanceErrorFixes :: Error -> Array FixSuggestion
generatePerformanceErrorFixes error =
  [ { description: "Optimize algorithm complexity"
    , fix: Nothing
    , confidence: 0.7
    , explanation: "Performance issues often stem from inefficient algorithms."
    }
  ]

-- | Generate fixes for test failures
generateTestFailureFixes :: Error -> Array FixSuggestion
generateTestFailureFixes error =
  [ { description: "Verify test expectations match implementation"
    , fix: Nothing
    , confidence: 0.8
    , explanation: "Test failures indicate mismatch between test and code."
    }
  ]

-- | Generate fixes for compile errors
generateCompileErrorFixes :: Error -> Array FixSuggestion
generateCompileErrorFixes error =
  [ { description: "Check for missing dependencies or imports"
    , fix: Nothing
    , confidence: 0.7
    , explanation: "Compilation errors often indicate missing dependencies."
    }
  ]

-- | Find related errors (similar patterns, same file, etc.)
findRelatedErrors :: Error -> Array Error
findRelatedErrors error =
  -- Would search error history for similar errors
  -- For now, return empty
  []

-- | Generate debugging steps
generateDebuggingSteps :: Error -> ErrorType -> Array String
generateDebuggingSteps error errorType =
  let baseSteps = case errorType of
        TypeError -> 
          [ "1. Check type annotations in the error location"
          , "2. Verify function signatures match usage"
          , "3. Check imports for correct types"
          ]
        SyntaxError ->
          [ "1. Check for mismatched brackets/parentheses"
          , "2. Verify string quotes are properly closed"
          , "3. Check for missing semicolons or commas"
          ]
        RuntimeError ->
          [ "1. Add logging around the error location"
          , "2. Check variable values before the error"
          , "3. Verify null/undefined checks"
          ]
        LogicError ->
          [ "1. Trace through the algorithm step by step"
          , "2. Check edge cases and boundary conditions"
          , "3. Verify expected vs actual outputs"
          ]
        SecurityError ->
          [ "1. Review security best practices"
          , "2. Check input validation"
          , "3. Verify authentication/authorization"
          ]
        PerformanceError ->
          [ "1. Profile the code to find bottlenecks"
          , "2. Check algorithm complexity"
          , "3. Look for unnecessary computations"
          ]
        TestFailure ->
          [ "1. Review test expectations"
          , "2. Check test data"
          , "3. Verify implementation matches requirements"
          ]
        CompileError ->
          [ "1. Check for missing dependencies"
          , "2. Verify build configuration"
          , "3. Check compiler version compatibility"
          ]
  in
    baseSteps <> 
    [ "4. Review recent changes that might have introduced the error"
    , "5. Check related files and dependencies"
    ]

-- | Determine error severity
determineSeverity :: Error -> ErrorType -> ErrorSeverity
determineSeverity error errorType =
  case errorType of
    SecurityError -> Critical
    RuntimeError -> High
    TypeError -> High
    SyntaxError -> Medium
    LogicError -> Medium
    PerformanceError -> Medium
    TestFailure -> Low
    CompileError -> High

-- | Get error patterns for a type
getErrorPatterns :: ErrorType -> Array ErrorPattern
getErrorPatterns errorType =
  case errorType of
    TypeError ->
      [ { pattern: "type mismatch"
        , category: TypeError
        , commonCause: "Types don't match expected signature"
        , typicalFix: "Update type annotations or convert types"
        }
      , { pattern: "cannot convert"
        , category: TypeError
        , commonCause: "Implicit conversion not allowed"
        , typicalFix: "Add explicit type conversion"
        }
      ]
    SyntaxError ->
      [ { pattern: "unexpected"
        , category: SyntaxError
        , commonCause: "Invalid syntax structure"
        , typicalFix: "Check syntax rules for the language"
        }
      ]
    RuntimeError ->
      [ { pattern: "null"
        , category: RuntimeError
        , commonCause: "Null value accessed"
        , typicalFix: "Add null check"
        }
      , { pattern: "undefined"
        , category: RuntimeError
        , commonCause: "Undefined value accessed"
        , typicalFix: "Initialize variable or add check"
        }
      ]
    _ -> []
