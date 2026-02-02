{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
module HigherKindedTypes where

import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import GHC.Core
import GHC.Core.Type
import GHC.Core.TyCon

-- | Higher-kinded type representation
data HKT = HKT
  { hktName :: T.Text
  , hktKind :: Kind
  , hktParams :: [T.Text]
  }

-- | Kind representation (type of types)
data Kind
  = KindStar  -- *
  = KindArrow Kind Kind  -- k1 -> k2
  | KindVar T.Text  -- k (kind variable)

-- | Extract higher-kinded types from Core
extractHKTs :: [CoreBind] -> [HKT]
extractHKTs binds = 
  let typeBindings = filter isTypeBinding binds
  in map extractHKT typeBindings
  where
    isTypeBinding (NonRec var _) = isTypeVar var
    isTypeBinding (Rec pairs) = any (isTypeVar . fst) pairs
    
    isTypeVar var = case splitTyConApp_maybe (varType var) of
      Just (tycon, _) -> isTypeConstructor tycon
      Nothing -> False

-- | Extract HKT from Core binding
extractHKT :: CoreBind -> HKT
extractHKT (NonRec var expr) =
  let name = T.pack $ show $ varName var
      kind = extractKind (varType var)
      params = extractTypeParams expr
  in HKT name kind params
extractHKT (Rec pairs) =
  let (var, expr) = head pairs
      name = T.pack $ show $ varName var
      kind = extractKind (varType var)
      params = extractTypeParams expr
  in HKT name kind params

-- | Extract kind from type
extractKind :: Type -> Kind
extractKind ty = case splitTyConApp_maybe ty of
  Just (tycon, _) -> tyConKind tycon
  Nothing -> KindStar

-- | Extract type parameters from expression
extractTypeParams :: CoreExpr -> [T.Text]
extractTypeParams expr = case expr of
  CoreLam v body -> 
    let param = T.pack $ show $ varName v
    in param : extractTypeParams body
  _ -> []

-- | Generate C++23 template for HKT
generateHKTTemplate :: HKT -> T.Text
generateHKTTemplate hkt = T.unlines
  [ "template<template<typename> class " <> hktName hkt <> ">"
  , "struct " <> hktName hkt <> "_Wrapper {"
  , "  template<typename T>"
  , "  using type = " <> hktName hkt <> "<T>;"
  , "};"
  ]

-- | Generate C++23 concept for HKT
generateHKTConcept :: HKT -> T.Text
generateHKTConcept hkt = T.unlines
  [ "template<template<typename> class F>"
  , "concept " <> hktName hkt <> "_Like = requires {"
  , "  typename F<int>;"
  , "  typename F<std::string>;"
  , "};"
  ]

-- | Map HKT to C++23 template
hktToCpp23 :: HKT -> T.Text
hktToCpp23 hkt = case hktKind hkt of
  KindStar -> 
    "template<typename T>\n" <>
    "using " <> hktName hkt <> " = T;"
  KindArrow KindStar KindStar ->
    "template<typename T>\n" <>
    "using " <> hktName hkt <> " = T;"
  KindArrow (KindArrow k1 k2) k3 ->
    "template<template<typename> class F>\n" <>
    "struct " <> hktName hkt <> " {\n" <>
    "  template<typename T>\n" <>
    "  using type = F<T>;\n" <>
    "};"
  _ -> 
    "template<typename T>\n" <>
    "using " <> hktName hkt <> " = T;"

-- | Common HKT patterns
data CommonHKT
  = Functor
  | Applicative
  | Monad
  | Traversable

-- | Generate C++23 for common HKTs
generateCommonHKT :: CommonHKT -> T.Text
generateCommonHKT Functor = T.unlines
  [ "template<template<typename> class F>"
  , "concept Functor = requires {"
  , "  template<typename T, typename U>"
  , "  requires std::convertible_to<T, U>"
  , "  F<U> fmap(F<T>, std::function<U(T)>);"
  , "};"
  ]

generateCommonHKT Applicative = T.unlines
  [ "template<template<typename> class F>"
  , "concept Applicative = Functor<F> && requires {"
  , "  template<typename T>"
  , "  F<T> pure(T);"
  , "  template<typename T, typename U>"
  , "  F<U> ap(F<std::function<U(T)>>, F<T>);"
  , "};"
  ]

generateCommonHKT Monad = T.unlines
  [ "template<template<typename> class F>"
  , "concept Monad = Applicative<F> && requires {"
  , "  template<typename T, typename U>"
  , "  F<U> bind(F<T>, std::function<F<U>(T)>);"
  , "};"
  ]

generateCommonHKT Traversable = T.unlines
  [ "template<template<typename> class F>"
  , "concept Traversable = Functor<F> && requires {"
  , "  template<template<typename> class G, typename T>"
  , "  requires Applicative<G>"
  , "  G<F<T>> sequence(F<G<T>>);"
  , "};"
  ]
