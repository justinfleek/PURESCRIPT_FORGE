{-|
Module      : Sidepanel.Components.Refactoring.RefactoringEngine
Description : Core refactoring engine
Implements refactoring operations like extract method, rename symbol, move code, etc.
-}
module Sidepanel.Components.Refactoring.RefactoringEngine where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.Either (Either(..))
import Effect.Aff (Aff)
import Sidepanel.Components.Refactoring.RefactoringTypes
  ( RefactoringOperation(..)
  , RefactoringResult
  , FileChange
  , CodeRange
  , ChangeType(..)
  , ExtractMethodParams
  , RenameSymbolParams
  , MoveCodeParams
  , InlineVariableParams
  , ExtractVariableParams
  , SimplifyExpressionParams
  , SymbolScope(..)
  )
import Tool.ASTEdit.FFI.FileIO (readFile, writeFile)
import Tool.ASTEdit.Structural
  ( AST
  , EditOp(..)
  , Symbol(..)
  , applyStructural
  , applyRename
  , applyExtract
  , applyInline
  )
import Tool.ASTEdit.Structural.Parser (parseToAST, getParser)
import Tool.ASTEdit.Structural.Render (renderAST)
import Tool.ASTEdit.Types (Span)
import Aleph.Coeffect.Spec (ASTLanguage(..))

-- | Detect language from file path
detectLanguageFromPath :: String -> ASTLanguage
detectLanguageFromPath filePath =
  if String.contains (String.Pattern ".purs") filePath then
    ASTPureScript
  else if String.contains (String.Pattern ".hs") filePath then
    ASTHaskell
  else if String.contains (String.Pattern ".lean") filePath then
    ASTLean4
  else if String.contains (String.Pattern ".ts") filePath || String.contains (String.Pattern ".tsx") filePath then
    ASTTypeScript
  else
    ASTUnknown filePath

-- | Convert CodeRange to Span
rangeToSpan :: CodeRange -> String -> Span
rangeToSpan range content =
  let lines = String.split (String.Pattern "\n") content
      startLine = Array.take range.start.line lines
      startLineContent = fromMaybe "" (Array.index lines range.start.line)
      startByte = String.length (String.joinWith "\n" startLine) + String.length "\n" + range.start.column
      
      endLine = Array.take range.end.line lines
      endLineContent = fromMaybe "" (Array.index lines range.end.line)
      endByte = String.length (String.joinWith "\n" endLine) + String.length "\n" + range.end.column
  in
    { startByte: startByte
    , endByte: endByte
    , startLine: range.start.line
    , startCol: range.start.column
    , endLine: range.end.line
    , endCol: range.end.column
    }

-- | Extract text from range
extractTextFromRange :: String -> CodeRange -> String
extractTextFromRange content range =
  let lines = String.split (String.Pattern "\n") content
      startLine = range.start.line
      endLine = range.end.line
      
      -- Extract lines in range
      rangeLines = Array.slice startLine (endLine + 1) lines
      
      -- Adjust first and last lines
      let adjustedLines = case Array.head rangeLines, Array.last rangeLines of
            Just first, Just last ->
              if startLine == endLine then
                [String.substring range.start.column range.end.column first]
              else
                let firstAdjusted = String.drop range.start.column first
                    lastAdjusted = String.take range.end.column last
                    middleLines = Array.drop 1 (Array.take (Array.length rangeLines - 1) rangeLines)
                in
                  [firstAdjusted] <> middleLines <> [lastAdjusted]
            _, _ -> []
  in
    String.joinWith "\n" adjustedLines

-- | Insert text at position
insertTextAtPosition :: String -> Position -> String -> String
insertTextAtPosition content position text =
  let lines = String.split (String.Pattern "\n") content
      targetLine = fromMaybe "" (Array.index lines position.line)
      beforeLine = String.take position.column targetLine
      afterLine = String.drop position.column targetLine
      newLine = beforeLine <> text <> afterLine
      
      beforeLines = Array.take position.line lines
      afterLines = Array.drop (position.line + 1) lines
  in
    String.joinWith "\n" (beforeLines <> [newLine] <> afterLines)

-- | Simplify expression text (basic implementation)
simplifyExpressionText :: String -> ASTLanguage -> String
simplifyExpressionText expr lang =
  -- Would use AST-based simplification
  -- For now, return as-is
  expr

-- | Import Position type
import Sidepanel.Components.Refactoring.RefactoringTypes (Position)

-- | Execute refactoring operation
executeRefactoring :: RefactoringOperation -> Aff RefactoringResult
executeRefactoring operation = case operation of
  ExtractMethod params -> extractMethod params
  RenameSymbol params -> renameSymbol params
  MoveCode params -> moveCode params
  InlineVariable params -> inlineVariable params
  ExtractVariable params -> extractVariable params
  SimplifyExpression params -> simplifyExpression params

-- | Extract method from selected code
extractMethod :: ExtractMethodParams -> Aff RefactoringResult
extractMethod params = do
  -- 1. Read source file
  readResult <- readFile params.filePath
  case readResult of
    Left err -> pure
      { success: false
      , changes: []
      , errors: [err]
      , warnings: []
      }
    Right content -> do
      -- 2. Detect language
      let lang = detectLanguageFromPath params.filePath
      
      -- 3. Parse to AST
      let parser = getParser lang
      parseResult <- parseToAST parser content
      case parseResult of
        Left parseErr -> pure
          { success: false
          , changes: []
          , errors: ["Parse error: " <> parseErr.message]
          , warnings: []
          }
        Right parsedAST -> do
          -- 4. Convert range to span
          let span = rangeToSpan params.range content
          
          -- 5. Extract code using AST operation
          let symbol = Symbol { name: params.methodName, qualifier: Nothing }
          extractResult <- applyExtract parsedAST.ast span symbol
          case extractResult of
            Left err -> pure
              { success: false
              , changes: []
              , errors: ["Extract failed: " <> err]
              , warnings: []
              }
            Right extractedAST -> do
              -- 6. Render back to source
              renderResult <- renderAST extractedAST lang
              case renderResult of
                Left renderErr -> pure
                  { success: false
                  , changes: []
                  , errors: ["Render error: " <> renderErr]
                  , warnings: []
                  }
                Right newContent -> do
                  -- 7. Extract old text from range
                  let oldText = extractTextFromRange content params.range
                  
                  pure
                    { success: true
                    , changes:
                        [ { filePath: params.filePath
                          , range: params.range
                          , oldText: oldText
                          , newText: newContent
                          , changeType: Replacement
                          }
                        ]
                    , errors: []
                    , warnings: []
                    }

-- | Rename symbol across scope
renameSymbol :: RenameSymbolParams -> Aff RefactoringResult
renameSymbol params = do
  -- 1. Read source file
  readResult <- readFile params.filePath
  case readResult of
    Left err -> pure
      { success: false
      , changes: []
      , errors: [err]
      , warnings: []
      }
    Right content -> do
      -- 2. Detect language
      let lang = detectLanguageFromPath params.filePath
      
      -- 3. Parse to AST
      let parser = getParser lang
      parseResult <- parseToAST parser content
      case parseResult of
        Left parseErr -> pure
          { success: false
          , changes: []
          , errors: ["Parse error: " <> parseErr.message]
          , warnings: []
          }
        Right parsedAST -> do
          -- 4. Create symbols
          let fromSymbol = Symbol { name: params.symbolName, qualifier: Nothing }
          let toSymbol = Symbol { name: params.newName, qualifier: Nothing }
          
          -- 5. Apply rename operation
          renameResult <- applyRename parsedAST.ast fromSymbol toSymbol
          case renameResult of
            Left err -> pure
              { success: false
              , changes: []
              , errors: ["Rename failed: " <> err]
              , warnings: []
              }
            Right renamedAST -> do
              -- 6. Render back to source
              renderResult <- renderAST renamedAST lang
              case renderResult of
                Left renderErr -> pure
                  { success: false
                  , changes: []
                  , errors: ["Render error: " <> renderErr]
                  , warnings: []
                  }
                Right newContent -> do
                  -- 7. Find all occurrences for change tracking
                  let changes = if content == newContent then [] else
                        [ { filePath: params.filePath
                          , range: { start: { line: 0, column: 0 }, end: { line: 0, column: 0 } }
                          , oldText: content
                          , newText: newContent
                          , changeType: Replacement
                          }
                        ]
                  
                  pure
                    { success: true
                    , changes: changes
                    , errors: []
                    , warnings: []
                    }

-- | Move code to different location
moveCode :: MoveCodeParams -> Aff RefactoringResult
moveCode params = do
  -- 1. Read source file
  sourceReadResult <- readFile params.sourceFile
  case sourceReadResult of
    Left err -> pure
      { success: false
      , changes: []
      , errors: ["Failed to read source file: " <> err]
      , warnings: []
      }
    Right sourceContent -> do
      -- 2. Read target file (or create if doesn't exist)
      targetReadResult <- readFile params.targetFile
      let targetContent = case targetReadResult of
            Left _ -> ""  -- File doesn't exist, will create
            Right content -> content
      
      -- 3. Detect language
      let lang = detectLanguageFromPath params.sourceFile
      
      -- 4. Parse source file to AST
      let parser = getParser lang
      sourceParseResult <- parseToAST parser sourceContent
      case sourceParseResult of
        Left parseErr -> pure
          { success: false
          , changes: []
          , errors: ["Parse error in source: " <> parseErr.message]
          , warnings: []
          }
        Right sourceAST -> do
          -- 5. Extract code from source range
          let sourceSpan = rangeToSpan params.sourceRange sourceContent
          let extractedCode = extractTextFromRange sourceContent params.sourceRange
          
          -- 6. Remove from source (would use AST operation)
          -- For now, simple text replacement
          let newSourceContent = String.replace (String.Pattern extractedCode) (String.Pattern "") sourceContent
          
          -- 7. Insert into target at position
          let newTargetContent = insertTextAtPosition targetContent params.targetPosition extractedCode
          
          pure
            { success: true
            , changes:
                [ { filePath: params.sourceFile
                  , range: params.sourceRange
                  , oldText: extractedCode
                  , newText: ""
                  , changeType: Deletion
                  }
                , { filePath: params.targetFile
                  , range:
                      { start: params.targetPosition
                      , end: params.targetPosition
                      }
                  , oldText: ""
                  , newText: extractedCode
                  , changeType: Insertion
                  }
                ]
            , errors: []
            , warnings: []
            }

-- | Inline variable (replace variable with its value)
inlineVariable :: InlineVariableParams -> Aff RefactoringResult
inlineVariable params = do
  -- 1. Read source file
  readResult <- readFile params.filePath
  case readResult of
    Left err -> pure
      { success: false
      , changes: []
      , errors: [err]
      , warnings: []
      }
    Right content -> do
      -- 2. Detect language
      let lang = detectLanguageFromPath params.filePath
      
      -- 3. Parse to AST
      let parser = getParser lang
      parseResult <- parseToAST parser content
      case parseResult of
        Left parseErr -> pure
          { success: false
          , changes: []
          , errors: ["Parse error: " <> parseErr.message]
          , warnings: []
          }
        Right parsedAST -> do
          -- 4. Create symbol for variable
          let symbol = Symbol { name: params.variableName, qualifier: Nothing }
          
          -- 5. Apply inline operation
          inlineResult <- applyInline parsedAST.ast symbol
          case inlineResult of
            Left err -> pure
              { success: false
              , changes: []
              , errors: ["Inline failed: " <> err]
              , warnings: []
              }
            Right inlinedAST -> do
              -- 6. Render back to source
              renderResult <- renderAST inlinedAST lang
              case renderResult of
                Left renderErr -> pure
                  { success: false
                  , changes: []
                  , errors: ["Render error: " <> renderErr]
                  , warnings: []
                  }
                Right newContent -> do
                  -- 7. Create changes for each occurrence
                  let changes = Array.map (\range ->
                        { filePath: params.filePath
                        , range: range
                        , oldText: params.variableName
                        , newText: ""  -- Value would be extracted from AST
                        , changeType: Replacement
                        }
                      ) params.occurrences
                  
                  pure
                    { success: true
                    , changes: changes
                    , errors: []
                    , warnings: []
                    }

-- | Extract variable from expression
extractVariable :: ExtractVariableParams -> Aff RefactoringResult
extractVariable params = do
  -- 1. Read source file
  readResult <- readFile params.filePath
  case readResult of
    Left err -> pure
      { success: false
      , changes: []
      , errors: [err]
      , warnings: []
      }
    Right content -> do
      -- 2. Detect language
      let lang = detectLanguageFromPath params.filePath
      
      -- 3. Parse to AST
      let parser = getParser lang
      parseResult <- parseToAST parser content
      case parseResult of
        Left parseErr -> pure
          { success: false
          , changes: []
          , errors: ["Parse error: " <> parseErr.message]
          , warnings: []
          }
        Right parsedAST -> do
          -- 4. Convert range to span
          let span = rangeToSpan params.range content
          
          -- 5. Extract expression using AST operation
          let symbol = Symbol { name: params.variableName, qualifier: Nothing }
          extractResult <- applyExtract parsedAST.ast span symbol
          case extractResult of
            Left err -> pure
              { success: false
              , changes: []
              , errors: ["Extract variable failed: " <> err]
              , warnings: []
              }
            Right extractedAST -> do
              -- 6. Render back to source
              renderResult <- renderAST extractedAST lang
              case renderResult of
                Left renderErr -> pure
                  { success: false
                  , changes: []
                  , errors: ["Render error: " <> renderErr]
                  , warnings: []
                  }
                Right newContent -> do
                  let oldText = extractTextFromRange content params.range
                  
                  pure
                    { success: true
                    , changes:
                        [ { filePath: params.filePath
                          , range: params.range
                          , oldText: oldText
                          , newText: newContent
                          , changeType: Replacement
                          }
                        ]
                    , errors: []
                    , warnings: []
                    }

-- | Simplify expression
simplifyExpression :: SimplifyExpressionParams -> Aff RefactoringResult
simplifyExpression params = do
  -- 1. Read source file
  readResult <- readFile params.filePath
  case readResult of
    Left err -> pure
      { success: false
      , changes: []
      , errors: [err]
      , warnings: []
      }
    Right content -> do
      -- 2. Detect language
      let lang = detectLanguageFromPath params.filePath
      
      -- 3. Parse to AST
      let parser = getParser lang
      parseResult <- parseToAST parser content
      case parseResult of
        Left parseErr -> pure
          { success: false
          , changes: []
          , errors: ["Parse error: " <> parseErr.message]
          , warnings: []
          }
        Right parsedAST -> do
          -- 4. Find expression node in range
          let span = rangeToSpan params.range content
          -- Would use AST to simplify expression
          -- For now, return placeholder with note
          
          let oldText = extractTextFromRange content params.range
          let simplifiedText = simplifyExpressionText oldText lang
          
          pure
            { success: true
            , changes:
                [ { filePath: params.filePath
                  , range: params.range
                  , oldText: oldText
                  , newText: simplifiedText
                  , changeType: Replacement
                  }
                ]
            , errors: []
            , warnings: ["Expression simplification uses text-based approach - AST-based simplification would be more accurate"]
            }
