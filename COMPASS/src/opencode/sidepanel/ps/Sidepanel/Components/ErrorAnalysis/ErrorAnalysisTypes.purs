{-|
Module      : Sidepanel.Components.ErrorAnalysis.ErrorAnalysisTypes
Description : Types for error analysis and debugging assistance
Types for error explanation, stack trace analysis, root cause detection, and fix suggestions.
-}
module Sidepanel.Components.ErrorAnalysis.ErrorAnalysisTypes where

import Prelude

-- | Error analysis result
type ErrorAnalysis =
  { error :: Error
  , explanation :: String
  , rootCause :: Maybe Location
  , suggestions :: Array FixSuggestion
  , relatedErrors :: Array Error
  , debuggingSteps :: Array String
  , severity :: ErrorSeverity
  }

-- | Error information
type Error =
  { message :: String
  , type_ :: ErrorType
  , location :: Maybe Location
  , stackTrace :: Maybe StackTrace
  , context :: ErrorContext
  }

-- | Error type
data ErrorType
  = CompileError
  | RuntimeError
  | TypeError
  | SyntaxError
  | LogicError
  | SecurityError
  | PerformanceError
  | TestFailure

derive instance eqErrorType :: Eq ErrorType

-- | Error severity
data ErrorSeverity
  = Critical
  | High
  | Medium
  | Low
  | Info

derive instance eqErrorSeverity :: Eq ErrorSeverity

-- | Location in code
type Location =
  { file :: String
  , line :: Int
  , column :: Int
  , endLine :: Maybe Int
  , endColumn :: Maybe Int
  }

-- | Stack trace
type StackTrace =
  { frames :: Array StackFrame
  , raw :: String
  }

-- | Stack frame
type StackFrame =
  { function :: Maybe String
  , file :: Maybe String
  , line :: Maybe Int
  , column :: Maybe Int
  , code :: Maybe String
  }

-- | Error context
type ErrorContext =
  { filePath :: String
  , language :: String
  , surroundingCode :: String  -- Code around error location
  , recentChanges :: Array FileChange
  , imports :: Array String
  }

-- | File change
type FileChange =
  { filePath :: String
  , changeType :: ChangeType
  , range :: CodeRange
  , oldText :: String
  , newText :: String
  }

-- | Change type
data ChangeType
  = Insertion
  | Deletion
  | Replacement

derive instance eqChangeType :: Eq ChangeType

-- | Code range
type CodeRange =
  { start :: { line :: Int, column :: Int }
  , end :: { line :: Int, column :: Int }
  }

-- | Fix suggestion
type FixSuggestion =
  { description :: String
  , fix :: Maybe CodeFix
  , confidence :: Number  -- 0.0 to 1.0
  , explanation :: String
  }

-- | Code fix
type CodeFix =
  { filePath :: String
  , range :: CodeRange
  , replacement :: String
  , diff :: String  -- Unified diff format
  }

-- | Error pattern
type ErrorPattern =
  { pattern :: String  -- Regex or pattern matcher
  , category :: ErrorType
  , commonCause :: String
  , typicalFix :: String
  }
