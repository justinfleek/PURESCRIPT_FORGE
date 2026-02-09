{-# LANGUAGE OverloadedStrings #-}
module ErrorHandling where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.List as L
import Parser

-- | Compilation error types
data CompileError
  = ParseError T.Text
  | TypeError T.Text
  | NameError T.Text
  | ImportError T.Text
  | CodeGenError T.Text
  deriving (Show, Eq)

-- | Error context for better error messages
data ErrorContext = ErrorContext
  { errorFile :: Maybe FilePath
  , errorLine :: Maybe Int
  , errorColumn :: Maybe Int
  , errorMessage :: T.Text
  , errorSuggestion :: Maybe T.Text
  }

-- | Format error message with context
formatError :: CompileError -> ErrorContext -> T.Text
formatError err ctx = T.unlines
  [ case errorFile ctx of
      Just f -> "Error in " <> T.pack f <> ":"
      Nothing -> "Error:"
  , case errorLine ctx of
      Just l -> "  Line " <> T.pack (show l) <> 
                case errorColumn ctx of
                  Just c -> ", column " <> T.pack (show c)
                  Nothing -> ""
      Nothing -> ""
  , "  " <> errorMessage ctx
  , case errorSuggestion ctx of
      Just s -> "  Suggestion: " <> s
      Nothing -> ""
  ]

-- | Collect all errors from compilation
type ErrorCollector = [CompileError]

-- | Result type with error collection
type CompileResult a = Either ErrorCollector a

-- | Add error to collector
addError :: CompileError -> ErrorCollector -> ErrorCollector
addError err errs = err : errs

-- | Check if result has errors
hasErrors :: CompileResult a -> Bool
hasErrors (Left _) = True
hasErrors (Right _) = False

-- | Get errors from result
getErrors :: CompileResult a -> ErrorCollector
getErrors (Left errs) = errs
getErrors (Right _) = []
