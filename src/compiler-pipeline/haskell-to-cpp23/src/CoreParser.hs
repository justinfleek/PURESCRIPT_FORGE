{-# LANGUAGE OverloadedStrings #-}
module CoreParser where

import qualified Data.Text as T
import GHC.Core
import GHC.Core.DataCon
import GHC.Types.Name
import GHC.Types.Var
import GHC.Types.Id

-- | GHC Core AST representation
data CoreExpr
  = CoreVar Var
  | CoreLit Literal
  | CoreApp CoreExpr CoreExpr
  | CoreLam Var CoreExpr
  | CoreLet [(Var, CoreExpr)] CoreExpr
  | CoreCase CoreExpr Var Type [CoreAlt]
  | CoreCast CoreExpr Coercion
  | CoreTick Tickish CoreExpr
  | CoreType Type
  | CoreCoercion Coercion

data CoreAlt = CoreAlt AltCon [Var] CoreExpr

-- | Extract Core from compiled Haskell module
extractCore :: ModGuts -> [CoreBind]
extractCore = mg_binds

-- | Convert Core expression to C++23
coreToCpp23 :: CoreExpr -> T.Text
coreToCpp23 (CoreVar v) = varToCpp v
coreToCpp23 (CoreLit lit) = literalToCpp lit
coreToCpp23 (CoreApp f x) = 
  coreToCpp23 f <> "(" <> coreToCpp23 x <> ")"
coreToCpp23 (CoreLam v body) =
  "[](" <> varToCpp v <> ") { return " <> coreToCpp23 body <> "; }"
coreToCpp23 (CoreLet binds body) =
  T.unlines (map (\(v, e) -> "auto " <> varToCpp v <> " = " <> coreToCpp23 e <> ";") binds) <>
  "return " <> coreToCpp23 body <> ";"
coreToCpp23 (CoreCase scrut var ty alts) =
  "std::visit([](auto&& v) {" <>
  T.unlines (map altToCpp alts) <>
  "}, " <> coreToCpp23 scrut <> ")"
coreToCpp23 (CoreCast expr _) = coreToCpp23 expr  -- Coercions are erased
coreToCpp23 (CoreTick _ expr) = coreToCpp23 expr  -- Ticks are erased
coreToCpp23 (CoreType _) = "/* type */"
coreToCpp23 (CoreCoercion _) = "/* coercion */"

altToCpp :: CoreAlt -> T.Text
altToCpp (CoreAlt con vars expr) =
  "  if constexpr (std::is_same_v<decltype(v), " <> conToCpp con <> ">) {" <>
  "    return " <> coreToCpp23 expr <> ";" <>
  "  }"

conToCpp :: AltCon -> T.Text
conToCpp (DataAlt dc) = dataConToCpp dc
conToCpp (LitAlt lit) = literalToCpp lit
conToCpp DEFAULT = "default"

dataConToCpp :: DataCon -> T.Text
dataConToCpp = T.pack . show . dataConName

varToCpp :: Var -> T.Text
varToCpp = T.pack . show . varName

literalToCpp :: Literal -> T.Text
literalToCpp (MachInt i) = T.pack (show i)
literalToCpp (MachInt64 i) = T.pack (show i) <> "LL"
literalToCpp (MachWord w) = T.pack (show w) <> "U"
literalToCpp (MachWord64 w) = T.pack (show w) <> "ULL"
literalToCpp (MachFloat f) = T.pack (show f) <> "f"
literalToCpp (MachDouble d) = T.pack (show d)
literalToCpp (MachChar c) = "\'" <> T.singleton c <> "\'"
literalToCpp (MachStr s) = "\"" <> T.pack s <> "\""
literalToCpp (MachNullAddr) = "nullptr"
literalToCpp (MachLabel _ _) = "/* label */"
literalToCpp (LitInteger i _) = T.pack (show i)
