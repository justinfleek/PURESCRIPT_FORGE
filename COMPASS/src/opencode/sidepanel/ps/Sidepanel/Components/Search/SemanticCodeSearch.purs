{-|
Module      : Sidepanel.Components.Search.SemanticCodeSearch
Description : Semantic code search - search by meaning, not just text
Implements semantic code search for finding code by meaning, patterns, and usage.
-}
module Sidepanel.Components.Search.SemanticCodeSearch where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.String.Pattern (Pattern(..))
import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Traversable (traverse)
import Data.Foldable (maximum, minimum)
import Tool.ASTEdit.FFI.FileIO (readFile)
import Tool.ASTEdit.Structural (AST, Node, NodeKind(..))
import Tool.ASTEdit.Structural.Parser (parseToAST, getParser)
import Tool.ASTEdit.Structural.Transform.NodeOps (findNodesByKind, findNodesByPredicate)
import Aleph.Coeffect.Spec (ASTLanguage(..))
import Opencode.Util.Filesystem (readDir, isFile, isDirectory)
import Sidepanel.Components.Search.SemanticCodeSearchTypes
  ( SemanticSearchQuery
  , SearchResult
  , SearchResultType(..)
  , PatternMatch
  , CodeSimilarity
  )

-- | Perform semantic search
semanticSearch :: SemanticSearchQuery -> Aff (Array SearchResult)
semanticSearch query = do
  -- Would use embeddings or semantic analysis
  -- For now, use pattern-based search as fallback
  patternSearch query

-- | Pattern-based search (fallback)
patternSearch :: SemanticSearchQuery -> Aff (Array SearchResult)
patternSearch query = do
  -- Extract keywords from query
  let keywords = extractKeywords query.text
  
  -- Search for patterns matching keywords
  let results = findPatternMatches keywords query.scope
  
  pure results

-- | Extract keywords from query
extractKeywords :: String -> Array String
extractKeywords text =
  let words = String.split (String.Pattern " ") text
      filtered = Array.filter (\w -> String.length w > 2) words
  in
    filtered

-- | Find pattern matches
findPatternMatches :: Array String -> Maybe String -> Array SearchResult
findPatternMatches keywords scopeM =
  -- Pattern matching searches for code that matches keywords
  -- Synchronous version - returns empty for now
  -- Full implementation would use Aff and traverse files
  []
  -- Note: Full implementation would be:
  -- findPatternMatchesAsync :: Array String -> Maybe String -> Aff (Array SearchResult)
  -- which would traverse files and search AST nodes

-- | Find similar code patterns
findSimilarCode :: String -> String -> Aff (Array CodeSimilarity)
findSimilarCode codeBlock language = do
  -- Use text similarity calculation
  let similarities = calculateTextSimilarity codeBlock
  pure similarities

-- | Calculate text similarity using simple metrics
calculateTextSimilarity :: String -> Array CodeSimilarity
calculateTextSimilarity codeBlock =
  -- Simplified similarity calculation using:
  -- 1. Token-based comparison (split by whitespace/punctuation)
  -- 2. Character n-gram comparison
  -- 3. Structural similarity (if AST available)
  -- For now, return empty array - would need codebase traversal
  []
  -- Full implementation would:
  -- 1. Tokenize input codeBlock
  -- 2. For each file in codebase:
  --    a. Tokenize file content
  --    b. Calculate similarity score (Jaccard, cosine, etc.)
  --    c. If similarity > threshold, add to results
  -- 3. Sort by similarity score descending

-- | Find code by pattern
findCodeByPattern :: String -> String -> Aff (Array PatternMatch)
findCodeByPattern pattern language = do
  -- Use text search for pattern matching
  let matches = findTextMatches pattern
  pure matches

-- | Find text matches using simple string search
findTextMatches :: String -> Array PatternMatch
findTextMatches pattern =
  -- Text-based pattern matching
  -- This would search codebase files for pattern occurrences
  -- For now, return empty array - would need file system access
  []
  -- Full implementation would:
  -- 1. Traverse codebase files
  -- 2. Read each file
  -- 3. Search for pattern (exact match or regex)
  -- 4. Return PatternMatch array with file, line, match, confidence

-- | Discover API functions
discoverAPIs :: String -> Maybe String -> Aff (Array SearchResult)
discoverAPIs query moduleM = do
  -- Get files to search
  let searchPath = fromMaybe "." moduleM
  files <- getAllSourceFiles searchPath
  
  -- Search each file for exported APIs
  results <- traverse (\file -> discoverAPIsInFile query file) files
  
  -- Filter and limit results
  let allResults = Array.concat results
      matching = Array.filter (\r -> String.contains (String.Pattern query) r.match) allResults
      limited = Array.take 50 matching  -- Limit to 50 results
  pure limited
  where
    getAllSourceFiles :: String -> Aff (Array String)
    getAllSourceFiles path = do
      -- Recursively find all source files
      isDir <- isDirectory path
      if isDir then
        traverseDirectory path
      else
        pure [path]
    
    traverseDirectory :: String -> Aff (Array String)
    traverseDirectory dir = do
      entries <- readDir dir
      case entries of
        Left _ -> pure []
        Right files -> do
          -- Filter source files
          let sourceFiles = Array.filter isSourceFile files
          -- Recursively traverse subdirectories
          subdirs <- Array.filterM isDirectory files
          subdirFiles <- traverse (\subdir -> traverseDirectory (dir <> "/" <> subdir)) subdirs
          pure (sourceFiles <> Array.concat subdirFiles)
    
    isSourceFile :: String -> Boolean
    isSourceFile file =
      String.contains (String.Pattern ".purs") file ||
      String.contains (String.Pattern ".hs") file ||
      String.contains (String.Pattern ".ts") file ||
      String.contains (String.Pattern ".tsx") file
    
    discoverAPIsInFile :: String -> String -> Aff (Array SearchResult)
    discoverAPIsInFile query file = do
      readResult <- readFile file
      case readResult of
        Left _ -> pure []
        Right content -> do
          -- Detect language and parse
          let lang = detectLanguageFromFile file
          let parser = getParser lang
          parseResult <- parseToAST parser content
          case parseResult of
            Left _ -> pure []
            Right parsed -> do
              -- Find export declarations
              let exports = findNodesByKind parsed.ast ExportDecl
              let functionDecls = findNodesByKind parsed.ast FunctionDecl
              let typeDecls = findNodesByKind parsed.ast TypeDecl
              
              -- Extract exported symbols
              let exportResults = Array.mapMaybe (\node -> 
                    extractExportResult node file query
                  ) exports
              let functionResults = Array.mapMaybe (\node ->
                    extractFunctionResult node file query
                  ) functionDecls
              let typeResults = Array.mapMaybe (\node ->
                    extractTypeResult node file query
                  ) typeDecls
              
              pure (exportResults <> functionResults <> typeResults)
    
    extractExportResult :: Node -> String -> String -> Maybe SearchResult
    extractExportResult node file query =
      if String.contains (String.Pattern query) node.text then
        Just
          { file: file
          , line: node.span.startLine
          , column: node.span.startCol
          , match: node.text
          , context: extractContext node.text
          , relevance: calculateRelevance query node.text
          , type_: FunctionsOnly
          }
      else
        Nothing
    
    extractFunctionResult :: Node -> String -> String -> Maybe SearchResult
    extractFunctionResult node file query =
      if String.contains (String.Pattern query) node.text then
        Just
          { file: file
          , line: node.span.startLine
          , column: node.span.startCol
          , match: node.text
          , context: extractContext node.text
          , relevance: calculateRelevance query node.text
          , type_: FunctionsOnly
          }
      else
        Nothing
    
    extractTypeResult :: Node -> String -> String -> Maybe SearchResult
    extractTypeResult node file query =
      if String.contains (String.Pattern query) node.text then
        Just
          { file: file
          , line: node.span.startLine
          , column: node.span.startCol
          , match: node.text
          , context: extractContext node.text
          , relevance: calculateRelevance query node.text
          , type_: TypesOnly
          }
      else
        Nothing
    
    extractContext :: String -> String
    extractContext text =
      -- Extract surrounding context (simplified - first 100 chars)
      String.take 100 text
    
    calculateRelevance :: String -> String -> Number
    calculateRelevance query text =
      -- Simple relevance: exact match = 1.0, contains = 0.5
      if query == text then 1.0
      else if String.contains (String.Pattern query) text then 0.5
      else 0.0
    
    detectLanguageFromFile :: String -> ASTLanguage
    detectLanguageFromFile file
      | String.contains (String.Pattern ".purs") file = ASTPureScript
      | String.contains (String.Pattern ".hs") file = ASTHaskell
      | String.contains (String.Pattern ".lean") file = ASTLean4
      | String.contains (String.Pattern ".ts") file || String.contains (String.Pattern ".tsx") file = ASTTypeScript
      | String.contains (String.Pattern ".py") file = ASTPython
      | otherwise = ASTUnknown file

-- | Find usage examples
findUsageExamples :: String -> String -> Aff (Array SearchResult)
findUsageExamples functionName language = do
  -- Get all files for the language
  let lang = detectLanguageFromExtension language
  files <- getAllFilesForLanguage lang
  
  -- Search each file for function usages
  results <- traverse (\file -> findUsagesInFile functionName file lang) files
  
  -- Limit results
  let allResults = Array.concat results
      limited = Array.take 20 allResults  -- Limit to 20 examples
  pure limited
  where
    detectLanguageFromExtension :: String -> ASTLanguage
    detectLanguageFromExtension lang = case lang of
      "purescript" -> ASTPureScript
      "haskell" -> ASTHaskell
      "lean" -> ASTLean4
      "typescript" -> ASTTypeScript
      "python" -> ASTPython
      _ -> ASTUnknown lang
    
    getAllFilesForLanguage :: ASTLanguage -> Aff (Array String)
    getAllFilesForLanguage lang = do
      let extension = getExtensionForLanguage lang
      getAllSourceFilesWithExtension extension
    
    getAllSourceFilesWithExtension :: String -> Aff (Array String)
    getAllSourceFilesWithExtension ext = do
      -- Start from current directory
      traverseDirectory "." ext
    
    traverseDirectory :: String -> String -> Aff (Array String)
    traverseDirectory dir ext = do
      entries <- readDir dir
      case entries of
        Left _ -> pure []
        Right files -> do
          -- Filter files with matching extension
          let matchingFiles = Array.filter (\f -> String.contains (String.Pattern ext) f) files
          let fullPaths = Array.map (\f -> dir <> "/" <> f) matchingFiles
          
          -- Recursively traverse subdirectories
          subdirs <- Array.filterM (\f -> isDirectory (dir <> "/" <> f)) files
          subdirFiles <- traverse (\subdir -> traverseDirectory (dir <> "/" <> subdir) ext) subdirs
          pure (fullPaths <> Array.concat subdirFiles)
    
    getExtensionForLanguage :: ASTLanguage -> String
    getExtensionForLanguage lang = case lang of
      ASTPureScript -> ".purs"
      ASTHaskell -> ".hs"
      ASTLean4 -> ".lean"
      ASTTypeScript -> ".ts"
      ASTPython -> ".py"
      _ -> ""
    
    findUsagesInFile :: String -> String -> ASTLanguage -> Aff (Array SearchResult)
    findUsagesInFile functionName file lang = do
      readResult <- readFile file
      case readResult of
        Left _ -> pure []
        Right content -> do
          let parser = getParser lang
          parseResult <- parseToAST parser content
          case parseResult of
            Left _ -> pure []
            Right parsed -> do
              -- Find Application nodes that might use this function
              let applications = findNodesByKind parsed.ast Application
              let usages = Array.mapMaybe (\node ->
                    if containsFunctionName node functionName then
                      Just
                        { file: file
                        , line: node.span.startLine
                        , column: node.span.startCol
                        , match: node.text
                        , context: extractContextAroundUsage content node.span.startLine
                        , relevance: 0.8  -- Usage examples are highly relevant
                        , type_: ExamplesOnly
                        }
                    else
                      Nothing
                  ) applications
              pure usages
    
    containsFunctionName :: Node -> String -> Boolean
    containsFunctionName node functionName =
      -- Check if node text or children contain function name
      String.contains (String.Pattern functionName) node.text ||
      Array.any (\child -> String.contains (String.Pattern functionName) child.text) node.children
    
    extractContextAroundUsage :: String -> Int -> String
    extractContextAroundUsage content lineNum =
      -- Extract lines around usage (simplified)
      let lines = String.split (String.Pattern "\n") content
          start = max 0 (lineNum - 2)
          end = min (Array.length lines) (lineNum + 3)
          contextLines = Array.slice start end lines
      in
        String.joinWith "\n" contextLines

-- | Search by meaning (semantic)
searchByMeaning :: String -> Aff (Array SearchResult)
searchByMeaning query = do
  -- Use keyword-based semantic search
  semanticSearch
    { text: query
    , scope: Nothing
    , language: Nothing
    , resultType: AllResults
    , maxResults: 10
    }

-- | Search for design patterns
searchDesignPatterns :: String -> Aff (Array SearchResult)
searchDesignPatterns patternName = do
  -- Get all source files
  files <- getAllSourceFiles "."
  
  -- Search each file for pattern
  results <- traverse (\file -> detectPatternInFile patternName file) files
  
  -- Filter and return matches
  let allResults = Array.concat results
      matching = Array.filter (\r -> r.relevance > 0.5) allResults
  pure matching
  where
    getAllSourceFiles :: String -> Aff (Array String)
    getAllSourceFiles path = do
      isDir <- isDirectory path
      if isDir then
        traverseDirectory path
      else
        pure [path]
    
    traverseDirectory :: String -> Aff (Array String)
    traverseDirectory dir = do
      entries <- readDir dir
      case entries of
        Left _ -> pure []
        Right files -> do
          let sourceFiles = Array.filter isSourceFile files
          let fullPaths = Array.map (\f -> dir <> "/" <> f) sourceFiles
          subdirs <- Array.filterM (\f -> isDirectory (dir <> "/" <> f)) files
          subdirFiles <- traverse (\subdir -> traverseDirectory (dir <> "/" <> subdir)) subdirs
          pure (fullPaths <> Array.concat subdirFiles)
    
    isSourceFile :: String -> Boolean
    isSourceFile file =
      String.contains (String.Pattern ".purs") file ||
      String.contains (String.Pattern ".hs") file ||
      String.contains (String.Pattern ".ts") file
    
    detectPatternInFile :: String -> String -> Aff (Array SearchResult)
    detectPatternInFile patternName file = do
      readResult <- readFile file
      case readResult of
        Left _ -> pure []
        Right content -> do
          -- Detect language and parse
          let lang = detectLanguageFromFile file
          let parser = getParser lang
          parseResult <- parseToAST parser content
          case parseResult of
            Left _ -> pure []
            Right parsed -> do
              -- Detect pattern based on AST structure
              let matches = detectPatternStructure parsed.ast patternName
              pure $ Array.map (\match ->
                { file: file
                , line: match.line
                , column: match.column
                , match: match.text
                , context: extractContext match.text
                , relevance: match.relevance
                , type_: AllResults
                }
              ) matches
    
    detectPatternStructure :: AST -> String -> Array { line :: Int, column :: Int, text :: String, relevance :: Number }
    detectPatternStructure ast patternName =
      -- Pattern detection based on AST structure
      -- Singleton: single instance variable, private constructor
      -- Factory: function that creates objects
      -- Observer: event listeners/subscribers
      case patternName of
        "Singleton" -> detectSingletonPattern ast
        "Factory" -> detectFactoryPattern ast
        "Observer" -> detectObserverPattern ast
        "Strategy" -> detectStrategyPattern ast
        _ -> []
    
    detectSingletonPattern :: AST -> Array { line :: Int, column :: Int, text :: String, relevance :: Number }
    detectSingletonPattern ast =
      -- Look for: private constructor, static instance variable
      let instances = findNodesByPredicate ast (\node ->
            node.kind == ValueDecl &&
            String.contains (String.Pattern "instance") node.text &&
            String.contains (String.Pattern "private") node.text
          )
      in
        Array.map (\node ->
          { line: node.span.startLine
          , column: node.span.startCol
          , text: node.text
          , relevance: 0.7
          }
        ) instances
    
    detectFactoryPattern :: AST -> Array { line :: Int, column :: Int, text :: String, relevance :: Number }
    detectFactoryPattern ast =
      -- Look for: functions that create and return objects
      let factories = findNodesByPredicate ast (\node ->
            node.kind == FunctionDecl &&
            (String.contains (String.Pattern "create") node.text ||
             String.contains (String.Pattern "make") node.text ||
             String.contains (String.Pattern "new") node.text)
          )
      in
        Array.map (\node ->
          { line: node.span.startLine
          , column: node.span.startCol
          , text: node.text
          , relevance: 0.6
          }
        ) factories
    
    detectObserverPattern :: AST -> Array { line :: Int, column :: Int, text :: String, relevance :: Number }
    detectObserverPattern ast =
      -- Look for: event listeners, subscribers, observers
      let observers = findNodesByPredicate ast (\node ->
            String.contains (String.Pattern "subscribe") node.text ||
            String.contains (String.Pattern "listen") node.text ||
            String.contains (String.Pattern "observer") node.text
          )
      in
        Array.map (\node ->
          { line: node.span.startLine
          , column: node.span.startCol
          , text: node.text
          , relevance: 0.6
          }
        ) observers
    
    detectStrategyPattern :: AST -> Array { line :: Int, column :: Int, text :: String, relevance :: Number }
    detectStrategyPattern ast =
      -- Look for: function parameters that are functions (strategy functions)
      let strategies = findNodesByPredicate ast (\node ->
            node.kind == FunctionDecl &&
            String.contains (String.Pattern "->") node.text &&
            Array.any (\child -> child.kind == Lambda) node.children
          )
      in
        Array.map (\node ->
          { line: node.span.startLine
          , column: node.span.startCol
          , text: node.text
          , relevance: 0.5
          }
        ) strategies
    
    detectLanguageFromFile :: String -> ASTLanguage
    detectLanguageFromFile file
      | String.contains (String.Pattern ".purs") file = ASTPureScript
      | String.contains (String.Pattern ".hs") file = ASTHaskell
      | String.contains (String.Pattern ".lean") file = ASTLean4
      | String.contains (String.Pattern ".ts") file = ASTTypeScript
      | otherwise = ASTUnknown file
    
    extractContext :: String -> String
    extractContext text = String.take 100 text

-- | Search for anti-patterns
searchAntiPatterns :: String -> Aff (Array SearchResult)
searchAntiPatterns antiPatternName = do
  -- Get all source files
  files <- getAllSourceFiles "."
  
  -- Detect anti-patterns in each file
  results <- traverse (\file -> detectAntiPatternInFile antiPatternName file) files
  
  -- Filter violations
  let allResults = Array.concat results
      violations = Array.filter (\r -> r.relevance > 0.5) allResults
  pure violations
  where
    getAllSourceFiles :: String -> Aff (Array String)
    getAllSourceFiles path = do
      isDir <- isDirectory path
      if isDir then
        traverseDirectory path
      else
        pure [path]
    
    traverseDirectory :: String -> Aff (Array String)
    traverseDirectory dir = do
      entries <- readDir dir
      case entries of
        Left _ -> pure []
        Right files -> do
          let sourceFiles = Array.filter isSourceFile files
          let fullPaths = Array.map (\f -> dir <> "/" <> f) sourceFiles
          subdirs <- Array.filterM (\f -> isDirectory (dir <> "/" <> f)) files
          subdirFiles <- traverse (\subdir -> traverseDirectory (dir <> "/" <> subdir)) subdirs
          pure (fullPaths <> Array.concat subdirFiles)
    
    isSourceFile :: String -> Boolean
    isSourceFile file =
      String.contains (String.Pattern ".purs") file ||
      String.contains (String.Pattern ".hs") file ||
      String.contains (String.Pattern ".ts") file
    
    detectAntiPatternInFile :: String -> String -> Aff (Array SearchResult)
    detectAntiPatternInFile antiPatternName file = do
      readResult <- readFile file
      case readResult of
        Left _ -> pure []
        Right content -> do
          let lang = detectLanguageFromFile file
          let parser = getParser lang
          parseResult <- parseToAST parser content
          case parseResult of
            Left _ -> pure []
            Right parsed -> do
              -- Detect anti-pattern based on name
              let violations = detectAntiPatternStructure parsed.ast antiPatternName content
              pure $ Array.map (\violation ->
                { file: file
                , line: violation.line
                , column: violation.column
                , match: violation.text
                , context: violation.context
                , relevance: violation.relevance
                , type_: AllResults
                }
              ) violations
    
    detectAntiPatternStructure :: AST -> String -> String -> Array { line :: Int, column :: Int, text :: String, context :: String, relevance :: Number }
    detectAntiPatternStructure ast antiPatternName content =
      case antiPatternName of
        "LongMethod" -> detectLongMethod ast content
        "GodObject" -> detectGodObject ast
        "SpaghettiCode" -> detectSpaghettiCode ast
        "DuplicateCode" -> detectDuplicateCode ast content
        _ -> []
    
    detectLongMethod :: AST -> String -> Array { line :: Int, column :: Int, text :: String, context :: String, relevance :: Number }
    detectLongMethod ast content =
      -- Methods longer than 50 lines are suspicious
      let functions = findNodesByKind ast FunctionDecl
          longFunctions = Array.filter (\node ->
            let lineCount = node.span.endLine - node.span.startLine
            in lineCount > 50
          ) functions
      in
        Array.map (\node ->
          { line: node.span.startLine
          , column: node.span.startCol
          , text: String.take 100 node.text
          , context: extractLines content node.span.startLine node.span.endLine
          , relevance: 0.7
          }
        ) longFunctions
    
    detectGodObject :: AST -> Array { line :: Int, column :: Int, text :: String, context :: String, relevance :: Number }
    detectGodObject ast =
      -- Objects/classes with many methods (>20) are suspicious
      let classes = findNodesByKind ast ClassDecl
          godObjects = Array.filter (\node ->
            let methodCount = Array.length (Array.filter (\child -> child.kind == FunctionDecl) node.children)
            in methodCount > 20
          ) classes
      in
        Array.map (\node ->
          { line: node.span.startLine
          , column: node.span.startCol
          , text: String.take 100 node.text
          , context: "Class with many methods"
          , relevance: 0.8
          }
        ) godObjects
    
    detectSpaghettiCode :: AST -> Array { line :: Int, column :: Int, text :: String, context :: String, relevance :: Number }
    detectSpaghettiCode ast =
      -- Deeply nested code (>5 levels) is suspicious
      let deepNodes = findDeeplyNestedNodes ast 5
      in
        Array.map (\node ->
          { line: node.span.startLine
          , column: node.span.startCol
          , text: String.take 100 node.text
          , context: "Deeply nested code"
          , relevance: 0.6
          }
        ) deepNodes
    
    detectDuplicateCode :: AST -> String -> Array { line :: Int, column :: Int, text :: String, context :: String, relevance :: Number }
    detectDuplicateCode ast content =
      -- Simplified: look for similar function signatures
      let functions = findNodesByKind ast FunctionDecl
          duplicates = findDuplicateSignatures functions
      in
        Array.map (\dup ->
          { line: dup.line
          , column: dup.column
          , text: dup.text
          , context: "Similar to other functions"
          , relevance: 0.5
          }
        ) duplicates
    
    findDeeplyNestedNodes :: AST -> Int -> Array Node
    findDeeplyNestedNodes ast maxDepth =
      findDeeplyNestedNodesRecursive ast.root 0 maxDepth
    
    findDeeplyNestedNodesRecursive :: Node -> Int -> Int -> Array Node
    findDeeplyNestedNodesRecursive node currentDepth maxDepth =
      let children = if currentDepth >= maxDepth then [node] else []
          childResults = Array.concatMap (\child ->
            findDeeplyNestedNodesRecursive child (currentDepth + 1) maxDepth
          ) node.children
      in
        children <> childResults
    
    findDuplicateSignatures :: Array Node -> Array { line :: Int, column :: Int, text :: String }
    findDuplicateSignatures functions =
      -- Group by signature similarity (simplified)
      let signatures = Array.map (\f -> extractSignature f) functions
          grouped = groupBySignature signatures
          duplicates = Array.filter (\group -> Array.length group > 1) grouped
      in
        Array.concatMap (\group ->
          Array.map (\sig -> { line: sig.line, column: sig.column, text: sig.text }) group
        ) duplicates
    
    extractSignature :: Node -> { line :: Int, column :: Int, text :: String, signature :: String }
    extractSignature node =
      -- Extract function signature (name and parameter count)
      let name = extractFunctionName node
          paramCount = Array.length (extractParametersFromNode node)
          signature = name <> "/" <> show paramCount
      in
        { line: node.span.startLine
        , column: node.span.startCol
        , text: node.text
        , signature: signature
        }
    
    groupBySignature :: Array { line :: Int, column :: Int, text :: String, signature :: String } -> Array (Array { line :: Int, column :: Int, text :: String, signature :: String })
    groupBySignature sigs =
      -- Group signatures by signature string
      -- Simple approach: collect unique signatures, then group
      let uniqueSigs = collectUniqueSignatures sigs
      in
        Array.mapMaybe (\sigStr ->
          let group = Array.filter (\s -> s.signature == sigStr) sigs
          in
            if Array.length group > 1 then Just group else Nothing
        ) uniqueSigs
    
    collectUniqueSignatures :: Array { line :: Int, column :: Int, text :: String, signature :: String } -> Array String
    collectUniqueSignatures sigs =
      -- Collect unique signature strings
      Array.foldl (\acc sig ->
        if Array.elem sig.signature acc then acc else Array.snoc acc sig.signature
      ) [] sigs
    
    extractFunctionName :: Node -> String
    extractFunctionName node =
      case Array.find (\child -> child.kind == Variable) node.children of
        Just varNode -> varNode.text
        Nothing -> "unnamed"
    
    extractParametersFromNode :: Node -> Array Node
    extractParametersFromNode node =
      Array.filter (\child ->
        child.kind == Variable ||
        child.kind == PatternVar
      ) node.children
    
    extractLines :: String -> Int -> Int -> String
    extractLines content startLine endLine =
      let lines = String.split (String.Pattern "\n") content
          extracted = Array.slice startLine (endLine + 1) lines
      in
        String.joinWith "\n" extracted
    
    detectLanguageFromFile :: String -> ASTLanguage
    detectLanguageFromFile file
      | String.contains (String.Pattern ".purs") file = ASTPureScript
      | String.contains (String.Pattern ".hs") file = ASTHaskell
      | String.contains (String.Pattern ".ts") file = ASTTypeScript
      | otherwise = ASTUnknown file
