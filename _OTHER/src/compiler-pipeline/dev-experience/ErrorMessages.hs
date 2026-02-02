{-# LANGUAGE OverloadedStrings #-}
-- Phase 7: Enhanced Error Messages
module ErrorMessages where

import qualified Data.Text as T
import qualified Data.List as L
import Parser (PSModule(..), PSDeclaration(..), PSExpression(..), parseModule)
import TypeChecker (typeCheckModule)

-- | Enhanced error message with context and suggestions
data EnhancedError = EnhancedError
  { errorMessage :: T.Text
  , errorRange :: Range
  , errorSeverity :: Severity
  , errorContext :: [ContextLine]
  , errorSuggestions :: [Suggestion]
  , errorCode :: ErrorCode
  }

data Range = Range
  { startLine :: Int
  , startColumn :: Int
  , endLine :: Int
  , endColumn :: Int
  }
  deriving (Show, Eq)

data Severity = Error | Warning | Info
  deriving (Show, Eq)

data ContextLine = ContextLine
  { contextLine :: Int
  , contextContent :: T.Text
  , contextHighlight :: Maybe (Int, Int)  -- (start, end) columns
  }
  deriving (Show, Eq)

data Suggestion = Suggestion
  { suggestionMessage :: T.Text
  , suggestionFix :: Maybe T.Text
  }
  deriving (Show, Eq)

data ErrorCode = ErrorCode
  { codeCategory :: T.Text
  , codeNumber :: Int
  }
  deriving (Show, Eq)

-- | Generate enhanced error message from parse error
generateParseError :: T.Text -> T.Text -> EnhancedError
generateParseError content errMsg =
  let lines = T.lines content
      -- Try to extract line number from error message
      lineNum = extractLineNumber errMsg
      range = Range lineNum 0 lineNum 100
      context = getContextLines content lineNum
      suggestions = getParseSuggestions errMsg
      code = ErrorCode "PARSE" 1001
  in EnhancedError errMsg range Error context suggestions code

-- | Generate enhanced error message from type error
generateTypeError :: PSModule -> T.Text -> T.Text -> EnhancedError
generateTypeError module' content errMsg =
  let lines = T.lines content
      -- Try to find the problematic declaration
      problemDecl = findProblematicDeclaration module' errMsg
      range = case problemDecl of
        Just decl -> getDeclarationRange decl content
        Nothing -> Range 0 0 0 0
      context = getContextLines content (startLine range)
      suggestions = getTypeSuggestions errMsg module'
      code = ErrorCode "TYPE" 2001
  in EnhancedError errMsg range Error context suggestions code

-- | Extract line number from error message
extractLineNumber :: T.Text -> Int
extractLineNumber msg =
  let words = T.words msg
      numbers = mapMaybe readMaybeInt words
  in case numbers of
    (n:_) -> n
    _ -> 0

-- | Get context lines around error
getContextLines :: T.Text -> Int -> [ContextLine]
getContextLines content lineNum =
  let lines = T.lines content
      start = max 0 (lineNum - 2)
      end = min (length lines - 1) (lineNum + 2)
      contextLines = take (end - start + 1) (drop start lines)
  in zipWith (\idx line -> ContextLine (start + idx) line Nothing) [0..] contextLines

-- | Get declaration range
getDeclarationRange :: PSDeclaration -> T.Text -> Range
getDeclarationRange decl content =
  let name = declarationName decl
      lines = T.lines content
      found = L.findIndex (T.isInfixOf name) lines
  in case found of
    Just lineNum ->
      let line = lines !! lineNum
          col = case T.findIndex (T.isPrefixOf name) (T.tails line) of
            Just idx -> idx
            Nothing -> 0
      in Range lineNum col lineNum (col + T.length name)
    Nothing -> Range 0 0 0 0

-- | Find problematic declaration from error message
findProblematicDeclaration :: PSModule -> T.Text -> Maybe PSDeclaration
findProblematicDeclaration module' errMsg =
  let decls = moduleDeclarations module'
      matches = filter (\d -> T.isInfixOf (declarationName d) errMsg) decls
  in L.head matches

-- | Get parse error suggestions
getParseSuggestions :: T.Text -> [Suggestion]
getParseSuggestions errMsg
  | T.isInfixOf "unexpected" errMsg =
      [ Suggestion "Check for missing semicolons or parentheses" Nothing
      , Suggestion "Verify syntax matches PureScript grammar" Nothing
      ]
  | T.isInfixOf "expecting" errMsg =
      [ Suggestion "Add the expected token" Nothing
      ]
  | otherwise = []

-- | Get type error suggestions
getTypeSuggestions :: T.Text -> PSModule -> [Suggestion]
getTypeSuggestions errMsg module'
  | T.isInfixOf "Undefined variable" errMsg =
      let varName = extractVariableName errMsg
          similar = findSimilarNames varName module'
      in [ Suggestion ("Did you mean one of: " <> T.unwords similar) Nothing
         ]
  | T.isInfixOf "Type mismatch" errMsg =
      [ Suggestion "Check type annotations match expression types" Nothing
      , Suggestion "Consider adding explicit type annotation" Nothing
      ]
  | otherwise = []

-- | Extract variable name from error message
extractVariableName :: T.Text -> T.Text
extractVariableName msg =
  let parts = T.splitOn ":" msg
  in if length parts > 1
    then T.strip (parts !! 1)
    else ""

-- | Find similar names in module
findSimilarNames :: T.Text -> PSModule -> [T.Text]
findSimilarNames target module' =
  let allNames = map declarationName (moduleDeclarations module')
      similar = filter (\n -> T.length n > 0 && 
                              (T.isPrefixOf target n || T.isPrefixOf n target ||
                               levenshteinDistance target n <= 2)) allNames
  in take 5 similar

-- | Levenshtein distance for name similarity
levenshteinDistance :: T.Text -> T.Text -> Int
levenshteinDistance s1 s2 =
  let s1' = T.unpack s1
      s2' = T.unpack s2
      n = length s1'
      m = length s2'
      d = [[0 | _ <- [0..m]] | _ <- [0..n]]
      d' = foldl (\acc i -> 
        foldl (\acc' j ->
          if i == 0 then acc' ++ [j]
          else if j == 0 then acc' ++ [i]
          else
            let cost = if s1' !! (i-1) == s2' !! (j-1) then 0 else 1
                val = minimum [acc' !! (j-1) + 1, acc !! j + 1, acc' !! (j-1) + cost]
            in acc' ++ [val]
          ) [] [0..m]
        ) [] [0..n]
  in if null d' then max (T.length s1) (T.length s2) else 0  -- Simplified

-- | Format error message for display
formatError :: EnhancedError -> T.Text
formatError err =
  let severityStr = case errorSeverity err of
        Error -> "Error"
        Warning -> "Warning"
        Info -> "Info"
      codeStr = codeCategory (errorCode err) <> "-" <> T.pack (show (codeNumber (errorCode err)))
      header = severityStr <> " [" <> codeStr <> "]: " <> errorMessage err
      contextStr = formatContext (errorContext err)
      suggestionsStr = formatSuggestions (errorSuggestions err)
  in header <> "\n\n" <> contextStr <> "\n" <> suggestionsStr

-- | Format context lines
formatContext :: [ContextLine] -> T.Text
formatContext lines =
  T.unlines $ map formatContextLine lines

formatContextLine :: ContextLine -> T.Text
formatContextLine ctx =
  let lineNum = T.pack (show (contextLine ctx))
      content = contextContent ctx
      highlight = case contextHighlight ctx of
        Just (start, end) -> highlightRange content start end
        Nothing -> content
  in lineNum <> " | " <> highlight

-- | Highlight range in text
highlightRange :: T.Text -> Int -> Int -> T.Text
highlightRange text start end =
  let before = T.take start text
      highlight = T.take (end - start) (T.drop start text)
      after = T.drop end text
  in before <> ">>>" <> highlight <> "<<<" <> after

-- | Format suggestions
formatSuggestions :: [Suggestion] -> T.Text
formatSuggestions [] = ""
formatSuggestions suggs =
  "Suggestions:\n" <> T.unlines (map formatSuggestion suggs)

formatSuggestion :: Suggestion -> T.Text
formatSuggestion sugg =
  "- " <> suggestionMessage sugg <>
  case suggestionFix sugg of
    Just fix -> "\n  Fix: " <> fix
    Nothing -> ""

-- | Get declaration name
declarationName :: PSDeclaration -> T.Text
declarationName (PSValueDecl decl) = valueName decl
declarationName (PSDataDecl decl) = dataName decl
declarationName (PSTypeDecl decl) = typeName decl
declarationName (PSClassDecl decl) = className decl
declarationName (PSInstanceDecl _) = ""

-- Helper for mapMaybe
mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe f = foldr (\x acc -> case f x of
  Just y -> y : acc
  Nothing -> acc) []

-- Helper for reading integers from text
readMaybeInt :: T.Text -> Maybe Int
readMaybeInt = either (const Nothing) Just . TR.decimal
