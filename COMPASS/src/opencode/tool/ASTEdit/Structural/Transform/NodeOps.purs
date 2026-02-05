{-|
Module      : Tool.ASTEdit.Structural.Transform.NodeOps
Description : Low-level AST node manipulation operations
= Node Operations

Low-level operations for manipulating AST nodes.
-}
module Tool.ASTEdit.Structural.Transform.NodeOps
  ( -- * Node Replacement
    replaceNode
  , replaceNodeBySpan
  , insertNode
  , removeNode
    -- * Node Traversal
  , traverseAST
  , findNodesByKind
  , findNodesByPredicate
    -- * Node Construction
  , mkVariableNode
  , mkApplicationNode
  , mkLambdaNode
  , mkLetNode
  , mkCaseNode
  , mkIfNode
  , mkLiteralNode
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Array as Array
import Tool.ASTEdit.Structural (AST, Node, NodeKind(..))
import Tool.ASTEdit.Types (Span)

-- ============================================================================
-- NODE REPLACEMENT
-- ============================================================================

-- | Replace a node in AST
replaceNode :: AST -> Node -> Node -> AST
replaceNode ast oldNode newNode =
  ast { root = replaceNodeInTree ast.root oldNode newNode }

replaceNodeInTree :: Node -> Node -> Node -> Node
replaceNodeInTree current oldNode newNode =
  if current == oldNode then
    newNode
  else
    current { children = Array.map (\child -> replaceNodeInTree child oldNode newNode) current.children }

-- | Replace node by span
replaceNodeBySpan :: AST -> Span -> Node -> AST
replaceNodeBySpan ast span newNode =
  case findNodeBySpanInTree ast.root span of
    Nothing -> ast
    Just oldNode -> replaceNode ast oldNode newNode

findNodeBySpanInTree :: Node -> Span -> Maybe Node
findNodeBySpanInTree node span =
  if spanMatches node.span span then
    Just node
  else
    Array.findMap (\child -> findNodeBySpanInTree child span) node.children

spanMatches :: Span -> Span -> Boolean
spanMatches s1 s2 =
  s1.startByte == s2.startByte && s1.endByte == s2.endByte

-- | Insert node as child
insertNode :: Node -> Node -> Int -> Node
insertNode parent child index =
  case Array.insertAt index child parent.children of
    Just newChildren -> parent { children = newChildren }
    Nothing -> parent { children = parent.children <> [child] }

-- | Remove node from parent
removeNode :: Node -> Node -> Node
removeNode parent child =
  parent { children = Array.filter (\c -> c /= child) parent.children }

-- ============================================================================
-- NODE TRAVERSAL
-- ============================================================================

-- | Traverse AST with function
traverseAST :: (Node -> Node) -> AST -> AST
traverseAST f ast =
  ast { root = traverseNode f ast.root }

traverseNode :: (Node -> Node) -> Node -> Node
traverseNode f node =
  f $ node { children = Array.map (traverseNode f) node.children }

-- | Find all nodes by kind
findNodesByKind :: AST -> NodeKind -> Array Node
findNodesByKind ast kind = findNodesByKindInTree ast.root kind

findNodesByKindInTree :: Node -> NodeKind -> Array Node
findNodesByKindInTree node kind =
  let matches = if node.kind == kind then [node] else []
      childMatches = Array.concatMap (\child -> findNodesByKindInTree child kind) node.children
  in matches <> childMatches

-- | Find nodes by predicate
findNodesByPredicate :: AST -> (Node -> Boolean) -> Array Node
findNodesByPredicate ast pred = findNodesByPredicateInTree ast.root pred

findNodesByPredicateInTree :: Node -> (Node -> Boolean) -> Array Node
findNodesByPredicateInTree node pred =
  let matches = if pred node then [node] else []
      childMatches = Array.concatMap (\child -> findNodesByPredicateInTree child pred) node.children
  in matches <> childMatches

-- ============================================================================
-- NODE CONSTRUCTION
-- ============================================================================

-- | Create variable node
mkVariableNode :: String -> Span -> Node
mkVariableNode name span =
  { kind: Variable
  , span: span
  , children: []
  , text: name
  , field: Nothing
  }

-- | Create application node
mkApplicationNode :: Node -> Node -> Span -> Node
mkApplicationNode func arg span =
  { kind: Application
  , span: span
  , children: [func, arg]
  , text: ""
  , field: Nothing
  }

-- | Create lambda node
mkLambdaNode :: Node -> Node -> Span -> Node
mkLambdaNode param body span =
  { kind: Lambda
  , span: span
  , children: [param, body]
  , text: ""
  , field: Nothing
  }

-- | Create let node
mkLetNode :: Array Node -> Node -> Span -> Node
mkLetNode bindings body span =
  { kind: LetExpr
  , span: span
  , children: bindings <> [body]
  , text: ""
  , field: Nothing
  }

-- | Create case node
mkCaseNode :: Node -> Array Node -> Span -> Node
mkCaseNode expr alternatives span =
  { kind: CaseExpr
  , span: span
  , children: [expr] <> alternatives
  , text: ""
  , field: Nothing
  }

-- | Create if node
mkIfNode :: Node -> Node -> Node -> Span -> Node
mkIfNode cond then_ else_ span =
  { kind: IfExpr
  , span: span
  , children: [cond, then_, else_]
  , text: ""
  , field: Nothing
  }

-- | Create literal node
mkLiteralNode :: String -> Span -> Node
mkLiteralNode value span =
  { kind: Literal
  , span: span
  , children: []
  , text: value
  , field: Nothing
  }
