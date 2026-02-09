{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
module TypeClassParser where

import qualified Data.Text as T
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import GHC.Core
import GHC.Core.Class
import GHC.Core.TyCon
import GHC.Core.Type
import GHC.Types.Var
import GHC.Types.Name
import GHC.Builtin.Types

-- | Type class information
data TypeClass = TypeClass
  { tcName :: T.Text
  , tcParams :: [T.Text]  -- Type parameters
  , tcMethods :: [Method]  -- Method signatures
  , tcSuperClasses :: [T.Text]  -- Superclass names
  }

-- | Method signature
data Method = Method
  { methodName :: T.Text
  , methodType :: T.Text  -- C++23 type signature
  }

-- | Type class instance
data TypeClassInstance = TypeClassInstance
  { instClass :: T.Text
  , instTypes :: [T.Text]  -- Instance types
  , instMethods :: Map.Map T.Text T.Text  -- Method implementations
  }

-- | Extract type classes from Core
extractTypeClasses :: [CoreBind] -> [TypeClass]
extractTypeClasses binds = 
  let classBindings = filter isClassBinding binds
  in map extractTypeClass classBindings
  where
    isClassBinding (NonRec var _) = isClassTyConType (varType var)
    isClassBinding (Rec pairs) = any (isClassTyConType . varType . fst) pairs
    
    isClassTyConType ty = case splitTyConApp_maybe ty of
      Just (tycon, _) -> isClassTyCon tycon
      Nothing -> False
    
    isClassTyCon tycon = 
      -- Simplified check: In practice, this would use GHC's Class structure
      -- For now, we'll extract type classes from bindings that have class-like structure
      -- This is a placeholder - actual implementation would check Class structure
      True  -- Will be refined when integrating with actual GHC Core extraction

-- | Extract type class from Core binding
extractTypeClass :: CoreBind -> TypeClass
extractTypeClass (NonRec var expr) = 
  let name = T.pack $ show $ varName var
      (params, methods) = extractClassInfo expr
  in TypeClass name params methods []
extractTypeClass (Rec pairs) = 
  let (var, expr) = head pairs
      name = T.pack $ show $ varName var
      (params, methods) = extractClassInfo expr
  in TypeClass name params methods []

-- | Extract class information from Core expression
extractClassInfo :: CoreExpr -> ([T.Text], [Method])
extractClassInfo expr = 
  case expr of
    CoreLam v body -> 
      let param = T.pack $ show $ varName v
          (params, methods) = extractClassInfo body
      in (param : params, methods)
    CoreApp (CoreApp (CoreVar f) _) methodExpr ->
      let methodName' = T.pack $ show $ varName f
          methodType' = extractMethodType methodExpr
          (params, methods) = extractClassInfo methodExpr
      in (params, Method methodName' methodType' : methods)
    CoreApp f x -> extractClassInfo f  -- Continue through applications
    _ -> ([], [])

-- | Extract method type from Core expression
extractMethodType :: CoreExpr -> T.Text
extractMethodType expr = 
  case expr of
    CoreLam v body -> 
      let argType = typeToCpp23 $ varType v
          retType = extractMethodType body
      in argType <> " -> " <> retType
    CoreVar v -> typeToCpp23 $ varType v
    CoreApp f _ -> extractMethodType f  -- Extract from function
    _ -> "auto"  -- Fallback for complex expressions

-- | Convert Haskell type to C++23 type
typeToCpp23 :: Type -> T.Text
typeToCpp23 ty
  | Just (tycon, args) <- splitTyConApp_maybe ty =
      case tyConName tycon of
        name | name == intTyConName -> "std::int64_t"
        name | name == doubleTyConName -> "double"
        name | name == charTyConName -> "char"
        name | name == boolTyConName -> "bool"
        name | name == listTyConName && length args == 1 ->
          "std::vector<" <> typeToCpp23 (head args) <> ">"
        name | name == maybeTyConName && length args == 1 ->
          "std::optional<" <> typeToCpp23 (head args) <> ">"
        name | name == eitherTyConName && length args == 2 ->
          "std::variant<" <> typeToCpp23 (args !! 0) <> ", " <> typeToCpp23 (args !! 1) <> ">"
        _ -> T.pack $ show ty
  | isFunTy ty =
      let (args, ret) = splitFunTys ty
          argTypes = map typeToCpp23 args
          retType = typeToCpp23 ret
      in "std::function<" <> retType <> "(" <> T.intercalate ", " argTypes <> ")>"
  | otherwise = T.pack $ show ty

-- | Generate C++20 concept from type class
generateConcept :: TypeClass -> T.Text
generateConcept tc = T.unlines
  [ "template<typename T>"
  , "concept " <> tcName tc <> " = requires(T t) {"
  , T.unlines $ map (generateRequirement (tcName tc)) (tcMethods tc)
  , "};"
  ]

-- | Generate requirement clause for concept
generateRequirement :: T.Text -> Method -> T.Text
generateRequirement className method = 
  "  { " <> methodName method <> "(t) } -> " <> parseReturnType (methodType method) <> ";"

-- | Parse return type from method type string
parseReturnType :: T.Text -> T.Text
parseReturnType ty = 
  case T.splitOn " -> " ty of
    [] -> "std::convertible_to<void>"
    [_] -> "std::convertible_to<void>"
    parts -> "std::convertible_to<" <> last parts <> ">"

-- | Generate type class instance as concept specialization
generateInstance :: TypeClassInstance -> T.Text
generateInstance inst = T.unlines
  [ "template<>"
  , "concept " <> instClass inst <> "<" <> T.intercalate ", " (instTypes inst) <> "> = true;"
  , ""
  , "// Instance methods"
  , T.unlines $ Map.foldMapWithKey generateInstanceMethod (instMethods inst)
  ]

-- | Generate instance method implementation
generateInstanceMethod :: T.Text -> T.Text -> T.Text
generateInstanceMethod name impl = 
  "inline auto " <> name <> "() { return " <> impl <> "; }"
