{-# LANGUAGE OverloadedStrings #-}
module TailCallOptimization where

import qualified Data.Text as T
import GHC.Core
import GHC.Core.DataCon

-- | Detect tail calls
isTailCall :: CoreExpr -> CoreExpr -> Bool
isTailCall function call = 
  case call of
    CoreApp f _ -> f == function
    _ -> False

-- | Optimize tail calls to loops
optimizeTailCalls :: CoreExpr -> CoreExpr
optimizeTailCalls expr = case expr of
  CoreLam v body -> CoreLam v (optimizeTailCalls body)
  CoreLet binds body -> CoreLet binds (optimizeTailCalls body)
  CoreCase scrut var ty alts -> 
    CoreCase scrut var ty (map optimizeAltTailCalls alts)
  CoreApp f x -> 
    if isTailCall f expr
    then convertToLoop expr
    else CoreApp (optimizeTailCalls f) (optimizeTailCalls x)
  _ -> expr

-- | Optimize tail calls in alternative
optimizeAltTailCalls :: CoreAlt -> CoreAlt
optimizeAltTailCalls (CoreAlt con vars expr) = 
  CoreAlt con vars (optimizeTailCalls expr)

-- | Convert tail-recursive function to loop
convertToLoop :: CoreExpr -> CoreExpr
convertToLoop expr = 
  -- This would convert tail recursion to a while loop
  -- For now, return optimized expression
  optimizeTailCalls expr

-- | Generate C++23 loop from tail-recursive function
generateTailCallLoop :: CoreExpr -> T.Text
generateTailCallLoop expr = case expr of
  CoreLam v body -> 
    let loopBody = extractLoopBody body
    in T.unlines
      [ "auto " <> varToCpp v <> " = /* initial value */;"
      , "while (true) {"
      , "  " <> loopBody
      , "}"
      ]
  _ -> "/* Not a tail-recursive function */"

-- | Extract loop body from tail-recursive function
extractLoopBody :: CoreExpr -> T.Text
extractLoopBody expr = case expr of
  CoreApp f x -> 
    if isSelfCall f
    then "break;  // Tail call optimized to loop"
    else coreExprToCpp23 expr
  CoreCase scrut var ty alts ->
    T.unlines
      [ "switch (" <> coreExprToCpp23 scrut <> ") {"
      , T.unlines $ map generateCaseBranch alts
      , "}"
      ]
  _ -> coreExprToCpp23 expr

-- | Check if function calls itself
isSelfCall :: CoreExpr -> Bool
isSelfCall (CoreVar v) = True  -- Simplified
isSelfCall _ = False

-- | Generate case branch
generateCaseBranch :: CoreAlt -> T.Text
generateCaseBranch (CoreAlt con vars expr) = 
  "  case " <> conToCpp23 con <> ": " <> extractLoopBody expr

-- | Generate optimized C++23 with tail call elimination
generateOptimizedCpp23 :: CoreExpr -> T.Text
generateOptimizedCpp23 expr = 
  let optimized = optimizeTailCalls expr
  in case optimized of
    CoreLam v body -> generateTailCallLoop optimized
    _ -> coreExprToCpp23 optimized

varToCpp :: Var -> T.Text
varToCpp = T.pack . show . varName

coreExprToCpp23 :: CoreExpr -> T.Text
coreExprToCpp23 (CoreVar v) = varToCpp v
coreExprToCpp23 (CoreLit lit) = literalToCpp23 lit
coreExprToCpp23 (CoreApp f x) = coreExprToCpp23 f <> "(" <> coreExprToCpp23 x <> ")"
coreExprToCpp23 (CoreLam v body) = "[](" <> varToCpp v <> ") { return " <> coreExprToCpp23 body <> "; }"
coreExprToCpp23 (CoreLet binds body) = 
  T.unlines (map (\(v, e) -> "auto " <> varToCpp v <> " = " <> coreExprToCpp23 e <> ";") binds) <>
  "return " <> coreExprToCpp23 body <> ";"
coreExprToCpp23 (CoreCase scrut var ty alts) =
  "std::visit([](auto&& v) -> auto {" <>
  T.unlines (map (\(CoreAlt con vars expr') -> 
    "  if constexpr (std::is_same_v<decltype(v), " <> conToCpp23 con <> ">) {" <>
    "    return " <> coreExprToCpp23 expr' <> ";" <>
    "  }") alts) <>
  "}, " <> coreExprToCpp23 scrut <> ")"
coreExprToCpp23 (CoreCast e _) = coreExprToCpp23 e
coreExprToCpp23 (CoreTick _ e) = coreExprToCpp23 e
coreExprToCpp23 (CoreType _) = "/* type */"
coreExprToCpp23 (CoreCoercion _) = "/* coercion */"

conToCpp23 :: AltCon -> T.Text
conToCpp23 (DataAlt dc) = T.pack $ show $ dataConName dc
conToCpp23 (LitAlt lit) = literalToCpp23 lit
conToCpp23 DEFAULT = "default"

literalToCpp23 :: Literal -> T.Text
literalToCpp23 (MachInt i) = T.pack $ show i
literalToCpp23 (MachInt64 i) = T.pack $ show i <> "LL"
literalToCpp23 (MachWord w) = T.pack $ show w <> "U"
literalToCpp23 (MachWord64 w) = T.pack $ show w <> "ULL"
literalToCpp23 (MachFloat f) = T.pack $ show f <> "f"
literalToCpp23 (MachDouble d) = T.pack $ show d
literalToCpp23 (MachChar c) = "\'" <> T.singleton c <> "\'"
literalToCpp23 (MachStr s) = "\"" <> T.pack s <> "\""
literalToCpp23 (MachNullAddr) = "nullptr"
literalToCpp23 (MachLabel _ _) = "/* label */"
literalToCpp23 (LitInteger i _) = T.pack $ show i
