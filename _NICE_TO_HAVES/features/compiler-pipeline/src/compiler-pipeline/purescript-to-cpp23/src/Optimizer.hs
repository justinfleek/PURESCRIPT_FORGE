{-# LANGUAGE OverloadedStrings #-}
module Optimizer where

import qualified Data.Text as T
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Parser

-- | Optimize PureScript AST before code generation
-- Phase 8: Production Readiness - Advanced Optimizations
optimizeModule :: PSModule -> PSModule
optimizeModule module'@PSModule{..} =
  let optimized = map optimizeDeclaration moduleDeclarations
      deadCodeEliminated = eliminateDeadCode optimized
      inlined = inlineSmallFunctions deadCodeEliminated
      constantFolded = foldConstants inlined
  in module' { moduleDeclarations = constantFolded }

-- | Optimize individual declaration
optimizeDeclaration :: PSDeclaration -> PSDeclaration
optimizeDeclaration (PSValueDecl decl) = 
  PSValueDecl decl { valueExpression = optimizeExpression (valueExpression decl) }
optimizeDeclaration decl = decl

-- | Optimize expression with multiple passes
optimizeExpression :: PSExpression -> PSExpression
optimizeExpression expr =
  let betaReduced = betaReduction expr
      inlined = inlineSimpleBindings betaReduced
      constantFolded = constantFolding inlined
      tailOptimized = tailCallOptimization constantFolded
  in tailOptimized

-- | Beta reduction: (\x -> body) arg -> body[x := arg]
betaReduction :: PSExpression -> PSExpression
betaReduction (PSApp (PSAbs params body) arg) =
  substitute params [arg] body
betaReduction (PSApp f x) =
  PSApp (betaReduction f) (betaReduction x)
betaReduction (PSLet bindings body) =
  PSLet (map (\(n, e) -> (n, betaReduction e)) bindings) (betaReduction body)
betaReduction expr = expr

-- | Inline simple bindings
inlineSimpleBindings :: PSExpression -> PSExpression
inlineSimpleBindings (PSLet bindings body) =
  if all isSimpleBinding bindings
    then inlineBindings bindings body
    else PSLet bindings body
inlineSimpleBindings expr = expr

-- | Constant folding
constantFolding :: PSExpression -> PSExpression
constantFolding (PSIf cond (PSLit (PSLitBoolean True)) elseExpr) = elseExpr
constantFolding (PSIf cond thenExpr (PSLit (PSLitBoolean False))) = thenExpr
constantFolding (PSIf (PSLit (PSLitBoolean True)) thenExpr _) = thenExpr
constantFolding (PSIf (PSLit (PSLitBoolean False)) _ elseExpr) = elseExpr
constantFolding (PSApp (PSVar "+") (PSLit (PSLitInt a), PSLit (PSLitInt b))) =
  PSLit (PSLitInt (a + b))
constantFolding (PSApp (PSVar "-") (PSLit (PSLitInt a), PSLit (PSLitInt b))) =
  PSLit (PSLitInt (a - b))
constantFolding (PSApp (PSVar "*") (PSLit (PSLitInt a), PSLit (PSLitInt b))) =
  PSLit (PSLitInt (a * b))
constantFolding expr = expr

-- | Tail call optimization
tailCallOptimization :: PSExpression -> PSExpression
tailCallOptimization expr = expr  -- Implemented in advanced-features/TailCallOptimization.hs

-- | Dead code elimination
eliminateDeadCode :: [PSDeclaration] -> [PSDeclaration]
eliminateDeadCode decls =
  let used = collectUsedNames decls
      isUsed name = Set.member name used
  in filter (\decl -> case decl of
    PSValueDecl d -> isUsed (valueName d)
    _ -> True) decls

-- | Collect all used names in declarations
collectUsedNames :: [PSDeclaration] -> Set.Set T.Text
collectUsedNames decls =
  let allNames = concatMap getUsedNames decls
  in Set.fromList allNames

-- | Get used names from declaration
getUsedNames :: PSDeclaration -> [T.Text]
getUsedNames (PSValueDecl decl) = getNamesFromExpr (valueExpression decl)
getUsedNames _ = []

-- | Get names from expression
getNamesFromExpr :: PSExpression -> [T.Text]
getNamesFromExpr (PSVar name) = [name]
getNamesFromExpr (PSApp f x) = getNamesFromExpr f ++ getNamesFromExpr x
getNamesFromExpr (PSAbs _ body) = getNamesFromExpr body
getNamesFromExpr (PSLet bindings body) =
  concatMap (getNamesFromExpr . snd) bindings ++ getNamesFromExpr body
getNamesFromExpr (PSCase expr alts) =
  getNamesFromExpr expr ++ concatMap (getNamesFromExpr . caseExpression) alts
getNamesFromExpr _ = []

-- | Inline small functions (heuristic: < 5 expressions)
inlineSmallFunctions :: [PSDeclaration] -> [PSDeclaration]
inlineSmallFunctions decls = decls  -- Conservative: don't inline by default

-- | Fold constants in declarations
foldConstants :: [PSDeclaration] -> [PSDeclaration]
foldConstants = map optimizeDeclaration

-- | Check if binding is simple (can be inlined)
isSimpleBinding :: (T.Text, PSExpression) -> Bool
isSimpleBinding (_, PSLit _) = True
isSimpleBinding (_, PSVar _) = True
isSimpleBinding (_, PSCon _) = True
isSimpleBinding _ = False

-- | Substitute variables in expression
substitute :: [T.Text] -> [PSExpression] -> PSExpression -> PSExpression
substitute params args expr = 
  foldl (\e (param, arg) -> substituteVar param arg e) expr (zip params args)

substituteVar :: T.Text -> PSExpression -> PSExpression -> PSExpression
substituteVar var replacement (PSVar v) | v == var = replacement
substituteVar var replacement (PSAbs params body) | var `notElem` params =
  PSAbs params (substituteVar var replacement body)
substituteVar var replacement (PSLet bindings body) =
  PSLet (map (\(n, e) -> (n, substituteVar var replacement e)) bindings)
        (if var `notElem` map fst bindings then substituteVar var replacement body else body)
substituteVar var replacement (PSApp f x) =
  PSApp (substituteVar var replacement f) (substituteVar var replacement x)
substituteVar var replacement (PSCase expr alts) =
  PSCase (substituteVar var replacement expr)
         (map (\alt -> alt { caseExpression = substituteVar var replacement (caseExpression alt) }) alts)
substituteVar var replacement expr = expr

-- | Inline bindings into expression
inlineBindings :: [(T.Text, PSExpression)] -> PSExpression -> PSExpression
inlineBindings bindings body =
  foldr (\(name, value) expr -> substituteVar name value expr) body bindings
