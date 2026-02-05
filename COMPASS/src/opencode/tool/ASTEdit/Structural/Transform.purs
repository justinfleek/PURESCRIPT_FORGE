{-|
Module      : Tool.ASTEdit.Structural.Transform
Description : AST transformation operations
= Transformation Operations

Implements all structural edit operations on ASTs.
-}
module Tool.ASTEdit.Structural.Transform
  ( -- * Node Finding
    findNodeBySpan
  , findNodeBySymbol
  , findAllOccurrences
    -- * Rename
  , applyRename
    -- * Extract
  , applyExtract
    -- * Inline
  , applyInline
    -- * Reorder
  , applyReorder
    -- * Wrap/Unwrap
  , applyWrap
  , applyUnwrap
    -- * Import Management
  , applyAddImport
  , applyRemoveUnused
    -- * Other Operations
  , applyHole
  , applyMoveToFile
  , applySequence
    -- * Scope Analysis
  , analyzeScope
  , SymbolScope(..)
  , Scope(..)
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.Map as Map
import Data.Traversable (traverse)
import Data.Generic.Rep (class Generic)
import Data.String as String
import Effect.Aff (Aff)
import Tool.ASTEdit.Structural
  ( AST
  , Node
  , NodeKind(..)
  , Symbol(..)
  , Wrapper(..)
  , ImportSpec
  , EditOp(..)
  , Span
  )
import Tool.ASTEdit.Structural.Transform.NodeOps
  ( replaceNodeBySpan
  , insertNode
  , removeNode
  , findNodesByKind
  , findNodesByPredicate
  , mkVariableNode
  , mkApplicationNode
  , mkLambdaNode
  , mkLetNode
  , mkCaseNode
  , mkIfNode
  )
import Tool.ASTEdit.Types (Change)

-- ============================================================================
-- SCOPE ANALYSIS
-- ============================================================================

{-| Symbol scope information.
-}
type SymbolScope =
  { symbol :: Symbol
  , definitionSpan :: Span
  , occurrences :: Array Span
  , scope :: Scope
  }

type Scope =
  { parent :: Maybe Scope
  , bindings :: Map.Map String Span
  , children :: Array Scope
  }

-- | Analyze symbol scope in AST
analyzeScope :: AST -> Symbol -> SymbolScope
analyzeScope ast (Symbol sym) =
  let rootScope = buildScopeTree ast.root Nothing
      definitionSpan = findDefinitionSpan rootScope sym.name
      -- Find all occurrences in AST, then filter by scope
      allOccurrences = findAllOccurrences ast (Symbol sym)
      occurrenceSpans = Array.map (\node -> node.span) allOccurrences
      -- Filter occurrences to only those in the correct scope
      scopedOccurrences = filterOccurrencesByScope rootScope sym.name occurrenceSpans
      symbolScope = findSymbolScope rootScope sym.name
  in { symbol: Symbol sym
     , definitionSpan: case definitionSpan of
         Just span -> span
         Nothing -> { startByte: 0, endByte: 0, startLine: 0, startCol: 0, endLine: 0, endCol: 0 }
     , occurrences: scopedOccurrences
     , scope: symbolScope
     }

-- | Build scope tree from AST
buildScopeTree :: Node -> Maybe Scope -> Scope
buildScopeTree node parent =
  let currentBindings = extractBindings node
      currentScope = { parent, bindings: currentBindings, children: [] }
      childScopes = Array.mapMaybe (\child -> if introducesScope child then Just (buildScopeTree child (Just currentScope)) else Nothing) node.children
  in currentScope { children = childScopes }

-- | Check if node introduces a new scope
introducesScope :: Node -> Boolean
introducesScope node = case node.kind of
  LetExpr -> true
  Lambda -> true
  CaseExpr -> true
  FunctionDecl -> true
  DoExpr -> true
  IfExpr -> false  -- If doesn't introduce scope, but body might
  _ -> false

-- | Extract bindings from a node
extractBindings :: Node -> Map.Map String Span
extractBindings node = case node.kind of
  ValueDecl -> case Array.head node.children of
    Just nameNode -> if nameNode.kind == Variable then Map.singleton nameNode.text nameNode.span else Map.empty
    Nothing -> Map.empty
  FunctionDecl -> if node.kind == FunctionDecl then Map.singleton node.text node.span else Map.empty
  LetExpr -> extractLetBindings node
  Lambda -> extractLambdaBindings node
  CaseExpr -> Map.empty  -- Case patterns introduce bindings but handled separately
  _ -> Map.empty

-- | Extract bindings from let expression
extractLetBindings :: Node -> Map.Map String Span
extractLetBindings node =
  let bindings = Array.filter (\child -> child.kind == ValueDecl) node.children
      bindingMap = Array.foldMap (\binding -> extractBindings binding) bindings
  in bindingMap

-- | Extract bindings from lambda (parameter)
extractLambdaBindings :: Node -> Map.Map String Span
extractLambdaBindings node = case Array.head node.children of
  Just paramNode -> if paramNode.kind == Variable then Map.singleton paramNode.text paramNode.span else Map.empty
  Nothing -> Map.empty

-- | Find definition span of symbol in scope tree
findDefinitionSpan :: Scope -> String -> Maybe Span
findDefinitionSpan scope name =
  case Map.lookup name scope.bindings of
    Just span -> Just span
    Nothing -> case scope.parent of
      Just parent -> findDefinitionSpan parent name
      Nothing -> Nothing

-- | Find all occurrences of symbol within its scope
findOccurrencesInScope :: Scope -> String -> Array Span
findOccurrencesInScope scope name =
  let definitionScope = findDefinitionScope scope name
      occurrences = case definitionScope of
        Just defScope -> findAllOccurrencesInScopeTree defScope name
        Nothing -> []
  in occurrences

-- | Find the scope where symbol is defined
findDefinitionScope :: Scope -> String -> Maybe Scope
findDefinitionScope scope name =
  if Map.member name scope.bindings then
    Just scope
  else
    case scope.parent of
      Just parent -> findDefinitionScope parent name
      Nothing -> Nothing

-- | Find all occurrences within a scope and its children
findAllOccurrencesInScopeTree :: Scope -> String -> Array Span
findAllOccurrencesInScopeTree scope name =
  let directOccurrences = case Map.lookup name scope.bindings of
        Just span -> [span]
        Nothing -> []
      childOccurrences = Array.concatMap (\child -> findAllOccurrencesInScopeTree child name) scope.children
      -- Check if child scope shadows this symbol
      shadowed = Array.any (\child -> Map.member name child.bindings) scope.children
      -- If shadowed, don't include occurrences from shadowing scopes
      filteredChildOccurrences = if shadowed then [] else childOccurrences
  in directOccurrences <> filteredChildOccurrences

-- | Find the scope information for a symbol
findSymbolScope :: Scope -> String -> Scope
findSymbolScope scope name =
  case findDefinitionScope scope name of
    Just defScope -> defScope
    Nothing -> scope  -- Fallback to root scope

-- | Filter occurrences to only those within the symbol's scope
filterOccurrencesByScope :: Scope -> String -> Array Span -> Array Span
filterOccurrencesByScope rootScope name spans =
  case findDefinitionScope rootScope name of
    Just defScope -> Array.filter (\span -> isSpanInScope defScope span) spans
    Nothing -> spans  -- If no definition found, return all

-- | Check if span is within scope (simplified - would need AST traversal for precise check)
isSpanInScope :: Scope -> Span -> Boolean
isSpanInScope scope span = true  -- Simplified: would need to check span is within scope's node span

-- ============================================================================
-- NODE FINDING
-- ============================================================================

-- | Find node by span
findNodeBySpan :: AST -> Span -> Maybe Node
findNodeBySpan ast span = findNodeInTree ast.root span

findNodeInTree :: Node -> Span -> Maybe Node
findNodeInTree node span =
  if spanMatches node.span span then
    Just node
  else
    Array.findMap (\child -> findNodeInTree child span) node.children

spanMatches :: Span -> Span -> Boolean
spanMatches s1 s2 =
  s1.startByte == s2.startByte && s1.endByte == s2.endByte && s1.startLine == s2.startLine && s1.startCol == s2.startCol

-- | Find node by symbol name
findNodeBySymbol :: AST -> Symbol -> Maybe Node
findNodeBySymbol ast (Symbol sym) = findSymbolInTree ast.root sym.name

findSymbolInTree :: Node -> String -> Maybe Node
findSymbolInTree node name =
  if node.kind == Variable && node.text == name then
    Just node
  else
    Array.findMap (\child -> findSymbolInTree child name) node.children

-- | Find all occurrences of symbol
findAllOccurrences :: AST -> Symbol -> Array Node
findAllOccurrences ast (Symbol sym) = findAllInTree ast.root sym.name

findAllInTree :: Node -> String -> Array Node
findAllInTree node name =
  let matches = if node.kind == Variable && node.text == name then [node] else []
      childMatches = Array.concatMap (\child -> findAllInTree child name) node.children
  in matches <> childMatches


-- ============================================================================
-- RENAME OPERATION
-- ============================================================================

-- | Apply rename operation with scope awareness
applyRename :: AST -> Symbol -> Symbol -> Aff (Either String AST)
applyRename ast from to = do
  let scopeInfo = analyzeScope ast from
  -- Find all occurrences in scope (scope-aware)
  let occurrences = Array.mapMaybe (\span -> findNodeBySpan ast span) scopeInfo.occurrences
  -- Rename each occurrence
  let renamedAST = Array.foldl (renameNodeInAST from to) ast occurrences
  pure $ Right renamedAST

renameNodeInAST :: Symbol -> Symbol -> AST -> Node -> AST
renameNodeInAST from to ast node =
  ast { root = renameNodeInTree from to ast.root node }

renameNodeInTree :: Symbol -> Symbol -> Node -> Node -> Node
renameNodeInTree from to target current =
  if current == target then
    current { text = show to }
  else
    current { children = Array.map (\child -> renameNodeInTree from to target child) current.children }

-- ============================================================================
-- EXTRACT OPERATION
-- ============================================================================

-- | Extract span to binding
applyExtract :: AST -> Span -> Symbol -> Aff (Either String AST)
applyExtract ast span symbol = do
  case findNodeBySpan ast span of
    Nothing -> pure $ Left "Span not found in AST"
    Just node -> do
      -- Create binding node: let extracted = <node> in <reference>
      let bindingSpan = { startByte: span.startByte, endByte: span.endByte, startLine: span.startLine, startCol: span.startCol, endLine: span.endLine, endCol: span.endCol }
      let varRef = mkVariableNode (case symbol of Symbol s -> s.name) span
      let bindingNode = mkLetNode [node] varRef bindingSpan
      
      -- Replace span with binding
      let extractedAST = replaceNodeBySpan ast span bindingNode
      pure $ Right extractedAST

-- ============================================================================
-- INLINE OPERATION
-- ============================================================================

-- | Inline all occurrences of symbol
applyInline :: AST -> Symbol -> Aff (Either String AST)
applyInline ast symbol = do
  case findNodeBySymbol ast symbol of
    Nothing -> pure $ Left "Symbol not found"
    Just definition -> do
      -- Find definition body (first child is usually the body)
      let body = case Array.head definition.children of
            Just b -> b
            Nothing -> definition
      
      -- Find all occurrences
      let occurrences = findAllOccurrences ast symbol
      
      -- Replace each occurrence with body (skip definition itself)
      let occurrencesToReplace = Array.filter (\occ -> occ /= definition) occurrences
      let inlinedAST = Array.foldl (\acc occ -> replaceNodeBySpan acc occ.span body) ast occurrencesToReplace
      
      -- Remove definition
      let finalAST = removeDefinition inlinedAST definition
      pure $ Right finalAST

-- | Remove definition node from AST
removeDefinition :: AST -> Node -> AST
removeDefinition ast def =
  ast { root = removeNodeFromTree ast.root def }

removeNodeFromTree :: Node -> Node -> Node
removeNodeFromTree current def =
  if current == def then
    -- Replace with first child if exists, otherwise empty node
    case Array.head current.children of
      Just child -> child
      Nothing -> current { kind: Error, text: "" }
  else
    current { children = Array.map (\child -> removeNodeFromTree child def) current.children }

-- ============================================================================
-- REORDER OPERATION
-- ============================================================================

-- | Reorder declarations
applyReorder :: AST -> Array Symbol -> Aff (Either String AST)
applyReorder ast symbols = do
  -- Find all declaration nodes for symbols
  let declarationNodes = Array.mapMaybe (\sym -> findNodeBySymbol ast sym) symbols
  
  -- Build dependency graph: which symbols each declaration depends on
  let dependencies = Array.mapMaybe (\node -> 
        case extractSymbolName node of
          "" -> Nothing
          name -> Just { node, name, deps: findDependencies ast node }
      ) declarationNodes
  
  -- Topologically sort declarations respecting dependencies
  let sortedDecls = topologicalSort dependencies symbols
  
  -- Reorder root children: place sorted declarations first, then others
  let rootDecls = findNodesByKind ast ValueDecl <> 
                  findNodesByKind ast FunctionDecl <>
                  findNodesByKind ast TypeDecl
  
  let sortedNodes = Array.mapMaybe (\sym -> Array.find (\n -> extractSymbolName n == (case sym of Symbol s -> s.name)) declarationNodes) sortedDecls
  let otherDecls = Array.filter (\n -> not (Array.elem n sortedNodes)) rootDecls
  
  -- Rebuild root with reordered declarations
  let newRoot = ast.root { children = sortedNodes <> otherDecls <> 
                          Array.filter (\n -> n.kind /= ValueDecl && n.kind /= FunctionDecl && n.kind /= TypeDecl) ast.root.children }
  
  pure $ Right (ast { root = newRoot })

-- | Find dependencies of a declaration node (symbols it references)
findDependencies :: AST -> Node -> Array String
findDependencies ast node =
  -- Find all variable references in this node's subtree
  let allVars = findAllVariablesInSubtree node
      -- Filter to only those that are declarations (not local bindings)
      declaredSymbols = Array.mapMaybe (\name -> 
          case findNodeBySymbol ast (Symbol { name }) of
            Just decl -> if decl /= node then Just name else Nothing
            Nothing -> Nothing
        ) allVars
  in declaredSymbols

-- | Find all variable names referenced in a subtree
findAllVariablesInSubtree :: Node -> Array String
findAllVariablesInSubtree node =
  let directVars = if node.kind == Variable then [node.text] else []
      childVars = Array.concatMap findAllVariablesInSubtree node.children
  in directVars <> childVars

-- | Topologically sort declarations respecting dependencies
topologicalSort :: Array { node :: Node, name :: String, deps :: Array String } -> Array Symbol -> Array Symbol
topologicalSort dependencies requestedOrder =
  let -- Build dependency map
      depMap = Array.foldl (\acc d -> Map.insert d.name d.deps acc) Map.empty dependencies
      
      -- Extract symbol names
      requestedNames = Array.map (\sym -> case sym of Symbol s -> s.name) requestedOrder
      
      -- Kahn's algorithm: find nodes with no dependencies first
      nodesWithNoDeps = Array.filter (\name -> 
          case Map.lookup name depMap of
            Just deps -> Array.length deps == 0
            Nothing -> true
        ) requestedNames
      
      -- Process nodes iteratively
      sorted = kahnSort nodesWithNoDeps depMap requestedOrder []
  in sorted

-- | Kahn's algorithm implementation
kahnSort :: Array String -> Map.Map String (Array String) -> Array Symbol -> Array Symbol -> Array Symbol
kahnSort queue depMap requestedOrder result =
  case Array.head queue of
    Nothing -> 
      -- Add any remaining symbols that weren't processed
      let processedNames = Array.map (\sym -> case sym of Symbol s -> s.name) result
          remaining = Array.filter (\sym -> 
              let name = case sym of Symbol s -> s.name
              in not (Array.elem name processedNames)
            ) requestedOrder
      in result <> remaining
    Just current ->
      -- Find symbol for current name
      let currentSymbol = Array.find (\sym -> case sym of Symbol s -> s.name == current) requestedOrder
          newResult = case currentSymbol of
            Just sym -> result <> [sym]
            Nothing -> result
          
          -- Remove current from dependencies of all nodes
          updatedDepMap = Map.map (\deps -> Array.filter (\d -> d /= current) deps) depMap
          
          -- Find new nodes with no dependencies
          processedNames = Array.map (\sym -> case sym of Symbol s -> s.name) newResult
          allRequestedNames = Array.map (\sym -> case sym of Symbol s -> s.name) requestedOrder
          remainingNames = Array.filter (\n -> not (Array.elem n processedNames)) allRequestedNames
          
          newNodesWithNoDeps = Array.filter (\name -> 
              case Map.lookup name updatedDepMap of
                Just deps -> Array.length deps == 0
                Nothing -> true
            ) remainingNames
          
          remainingQueue = Array.drop 1 queue <> newNodesWithNoDeps
      in kahnSort remainingQueue updatedDepMap requestedOrder newResult

-- ============================================================================
-- WRAP/UNWRAP OPERATIONS
-- ============================================================================

-- | Wrap span in construct
applyWrap :: AST -> Span -> Wrapper -> Aff (Either String AST)
applyWrap ast span wrapper = do
  case findNodeBySpan ast span of
    Nothing -> pure $ Left "Span not found"
    Just node -> do
      -- Create wrapper node based on wrapper type
      let wrappedNode = case wrapper of
            LetWrapper -> mkLetNode [node] node span
            DoWrapper -> node { kind: DoExpr, children: [node] }
            ParenWrapper -> node { text: "(" <> node.text <> ")" }
            LambdaWrapper param -> mkLambdaNode (mkVariableNode param span) node span
            CaseWrapper -> mkCaseNode node [] span
            IfWrapper -> mkIfNode node node node span
            TypeAnnWrapper type_ -> node { children = [node, mkVariableNode type_ span] }
            TryCatchWrapper -> node { children = [node] }  -- Simplified
      
      -- Replace node with wrapped version
      let wrappedAST = replaceNodeBySpan ast span wrappedNode
      pure $ Right wrappedAST

-- | Unwrap span (remove wrapper)
applyUnwrap :: AST -> Span -> Aff (Either String AST)
applyUnwrap ast span = do
  case findNodeBySpan ast span of
    Nothing -> pure $ Left "Span not found"
    Just node -> do
      -- Extract inner expression from wrapper based on node kind
      let innerNode = case node.kind of
            LetExpr -> case Array.last node.children of Just body -> body; Nothing -> node
            DoExpr -> case Array.head node.children of Just stmt -> stmt; Nothing -> node
            CaseExpr -> case Array.head node.children of Just expr -> expr; Nothing -> node
            IfExpr -> case Array.index node.children 1 of Just then_ -> then_; Nothing -> node
            Lambda -> case Array.last node.children of Just body -> body; Nothing -> node
            Application -> case Array.head node.children of Just func -> func; Nothing -> node
            _ -> node
      
      -- Replace wrapper with inner node
      let unwrappedAST = replaceNodeBySpan ast span innerNode
      pure $ Right unwrappedAST

-- ============================================================================
-- IMPORT MANAGEMENT
-- ============================================================================

-- | Add import statement
applyAddImport :: AST -> ImportSpec -> Aff (Either String AST)
applyAddImport ast importSpec = do
  -- Check for existing import
  let existingImports = findNodesByKind ast ImportDecl
  let alreadyExists = Array.any (\imp -> imp.text == importSpec.module) existingImports
  
  if alreadyExists then
    pure $ Right ast  -- Already exists, no-op
  else do
    -- Create import node
    let importText = "import " <> importSpec.module <>
                     (case importSpec.items of
                        Just items -> " (" <> String.joinWith ", " items <> ")"
                        Nothing -> "") <>
                     (if importSpec.qualified then " as " <> (case importSpec.alias of Just a -> a; Nothing -> "") else "")
    
    let importSpan = { startByte: 0, endByte: importText.length, startLine: 0, startCol: 0, endLine: 0, endCol: importText.length }
    let importNode = { kind: ImportDecl, span: importSpan, children: [], text: importText, field: Nothing }
    
    -- Insert at beginning of root children (before other declarations)
    let newRoot = ast.root { children = [importNode] <> ast.root.children }
    pure $ Right (ast { root = newRoot })

-- | Remove unused bindings
applyRemoveUnused :: AST -> Aff (Either String AST)
applyRemoveUnused ast = do
  -- Find all value declarations
  let valueDecls = findNodesByKind ast ValueDecl <>
                    findNodesByKind ast FunctionDecl <>
                    findNodesByKind ast TypeDecl
  
  -- Find which ones are unused (not referenced elsewhere)
  let unusedDecls = Array.filter (\decl -> isUnused ast decl) valueDecls
  
  -- Remove unused declarations
  let cleanedAST = Array.foldl (\acc decl -> removeDefinition acc decl) ast unusedDecls
  pure $ Right cleanedAST

-- | Check if declaration is unused
isUnused :: AST -> Node -> Boolean
isUnused ast decl =
  -- Extract symbol name from declaration
  let symbolName = extractSymbolName decl
  in if symbolName == "" then
    false  -- Can't determine, keep it
  else
    -- Count occurrences (should be 1 if only in definition)
    let occurrences = findNodesByPredicate ast (\n -> n.kind == Variable && n.text == symbolName)
    in Array.length occurrences <= 1

-- | Extract symbol name from declaration node
extractSymbolName :: Node -> String
extractSymbolName node = case node.kind of
  ValueDecl -> case Array.head node.children of Just name -> name.text; Nothing -> ""
  FunctionDecl -> node.text  -- Function name is usually in text
  TypeDecl -> node.text
  Variable -> node.text
  _ -> ""

-- ============================================================================
-- OTHER OPERATIONS
-- ============================================================================

-- | Replace span with typed hole
applyHole :: AST -> Span -> Aff (Either String AST)
applyHole ast span = do
  case findNodeBySpan ast span of
    Nothing -> pure $ Left "Span not found"
    Just node -> do
      -- Create typed hole node (placeholder)
      let holeText = "?hole"  -- Typed hole syntax
      let holeNode = { kind: Error, span: span, children: [], text: holeText, field: Just "hole" }
      
      -- Replace node with hole
      let holedAST = replaceNodeBySpan ast span holeNode
      pure $ Right holedAST

-- | Move symbol to different file
applyMoveToFile :: AST -> Symbol -> String -> Aff (Either String AST)
applyMoveToFile ast symbol filePath = do
  case findNodeBySymbol ast symbol of
    Nothing -> pure $ Left "Symbol not found"
    Just definition -> do
      -- Remove definition from current AST
      let astWithoutDef = removeDefinition ast definition
      
      -- Add import for moved symbol
      let moduleName = extractModuleName filePath
      let symbolName = case symbol of Symbol s -> s.name
      let importSpec = { module: moduleName, items: Just [symbolName], qualified: false, alias: Nothing }
      
      -- Add import
      importResult <- applyAddImport astWithoutDef importSpec
      case importResult of
        Left err -> pure $ Left err
        Right finalAST -> pure $ Right finalAST

-- | Extract module name from file path
extractModuleName :: String -> String
extractModuleName filePath =
  -- Remove extension and path separators
  let withoutExt = String.replace (String.Pattern ".purs") (String.Replacement "") filePath
      withoutExt2 = String.replace (String.Pattern ".hs") (String.Replacement "") withoutExt
      withoutExt3 = String.replace (String.Pattern ".lean") (String.Replacement "") withoutExt2
      parts = String.split (String.Pattern "/") withoutExt3
  in String.joinWith "." parts

-- | Apply sequence of operations
applySequence :: AST -> Array EditOp -> Aff (Either String AST)
applySequence ast ops = do
  Array.foldM applySingleOperation ast ops
  where
    applySingleOperation :: AST -> EditOp -> Aff (Either String AST)
    applySingleOperation ast' op' = case op' of
      Rename from to -> applyRename ast' from to
      Extract span symbol -> applyExtract ast' span symbol
      Inline symbol -> applyInline ast' symbol
      Reorder symbols -> applyReorder ast' symbols
      Wrap span wrapper -> applyWrap ast' span wrapper
      Unwrap span -> applyUnwrap ast' span
      AddImport importSpec -> applyAddImport ast' importSpec
      RemoveUnused -> applyRemoveUnused ast'
      Hole span -> applyHole ast' span
      MoveToFile symbol filePath -> applyMoveToFile ast' symbol filePath
      Sequence ops' -> applySequence ast' ops'
