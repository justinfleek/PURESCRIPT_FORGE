{-# LANGUAGE OverloadedStrings #-}
module PatternOptimization where

import qualified Data.Text as T
import Data.List (partition)
import GHC.Core
import GHC.Core.DataCon

-- | Pattern matching optimization
optimizePatternMatching :: CoreExpr -> CoreExpr
optimizePatternMatching expr = case expr of
  CoreCase scrut var ty alts -> optimizeCase scrut var ty alts
  CoreApp f x -> CoreApp (optimizePatternMatching f) (optimizePatternMatching x)
  CoreLam v body -> CoreLam v (optimizePatternMatching body)
  CoreLet binds body -> CoreLet binds (optimizePatternMatching body)
  _ -> expr

-- | Optimize case expression
optimizeCase :: CoreExpr -> Var -> Type -> [CoreAlt] -> CoreExpr
optimizeCase scrut var ty alts =
  let optimizedAlts = optimizeAlts alts
      -- Reorder alternatives for better matching
      reorderedAlts = reorderAlts optimizedAlts
  in CoreCase scrut var ty reorderedAlts

-- | Optimize alternatives
optimizeAlts :: [CoreAlt] -> [CoreAlt]
optimizeAlts = map optimizeAlt

-- | Optimize single alternative
optimizeAlt :: CoreAlt -> CoreAlt
optimizeAlt (CoreAlt con vars expr) = 
  CoreAlt con vars (optimizePatternMatching expr)

-- | Reorder alternatives for optimal matching
reorderAlts :: [CoreAlt] -> [CoreAlt]
reorderAlts alts = 
  -- Put DEFAULT last, literals before constructors
  let (defaults, nonDefaults) = partition isDefault alts
      (literals, constructors) = partition isLiteral nonDefaults
  in constructors ++ literals ++ defaults
  where
    isDefault (CoreAlt DEFAULT _ _) = True
    isDefault _ = False
    
    isLiteral (CoreAlt (LitAlt _) _ _) = True
    isLiteral _ = False

-- | Generate optimized C++23 pattern matching
generateOptimizedPatternMatching :: CoreExpr -> T.Text
generateOptimizedPatternMatching expr = case expr of
  CoreCase scrut var ty alts ->
    let optimized = optimizeCase scrut var ty alts
    in generateCaseCpp23 optimized
  _ -> "/* Not a case expression */"

-- | Generate C++23 for optimized case
generateCaseCpp23 :: CoreExpr -> T.Text
generateCaseCpp23 (CoreCase scrut var ty alts) = T.unlines
  [ "std::visit([](auto&& v) -> auto {"
  , T.unlines $ map generateAltCpp23 alts
  , "}, " <> coreExprToCpp23 scrut <> ")"
  ]
generateCaseCpp23 _ = "/* Invalid case */"

-- | Generate C++23 for alternative
generateAltCpp23 :: CoreAlt -> T.Text
generateAltCpp23 (CoreAlt con vars expr) = 
  "  if constexpr (std::is_same_v<decltype(v), " <> conToCpp23 con <> ">) {" <>
  "    return " <> coreExprToCpp23 expr <> ";" <>
  "  }"

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

coreExprToCpp23 :: CoreExpr -> T.Text
coreExprToCpp23 (CoreVar v) = T.pack $ show $ varName v
coreExprToCpp23 (CoreLit lit) = literalToCpp23 lit
coreExprToCpp23 (CoreApp f x) = coreExprToCpp23 f <> "(" <> coreExprToCpp23 x <> ")"
coreExprToCpp23 (CoreLam v body) = "[](" <> T.pack (show $ varName v) <> ") { return " <> coreExprToCpp23 body <> "; }"
coreExprToCpp23 (CoreLet binds body) = 
  T.unlines (map (\(v, e) -> "auto " <> T.pack (show $ varName v) <> " = " <> coreExprToCpp23 e <> ";") binds) <>
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
