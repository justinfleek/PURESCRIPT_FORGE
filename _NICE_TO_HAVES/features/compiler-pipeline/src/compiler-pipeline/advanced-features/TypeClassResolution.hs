{-# LANGUAGE OverloadedStrings #-}
module TypeClassResolution where

import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import TypeClassParser

-- | Type class instance resolution context
data ResolutionContext = ResolutionContext
  { availableInstances :: Map.Map T.Text [TypeClassInstance]
  , constraints :: [T.Text]
  , resolved :: Map.Map T.Text TypeClassInstance
  }

-- | Resolve type class instances
resolveInstances :: ResolutionContext -> [T.Text] -> Either T.Text ResolutionContext
resolveInstances ctx constraints' = 
  let ctx' = ctx { constraints = constraints' }
  in foldM resolveConstraint ctx' constraints'

-- | Resolve a single constraint
resolveConstraint :: ResolutionContext -> T.Text -> Either T.Text ResolutionContext
resolveConstraint ctx constraint = 
  case Map.lookup constraint (availableInstances ctx) of
    Just instances -> 
      case findMatchingInstance instances constraint of
        Just inst -> Right $ ctx { resolved = Map.insert constraint inst (resolved ctx) }
        Nothing -> Left $ "No matching instance for: " <> constraint
    Nothing -> Left $ "Unknown type class: " <> constraint

-- | Find matching instance for constraint
findMatchingInstance :: [TypeClassInstance] -> T.Text -> Maybe TypeClassInstance
findMatchingInstance instances constraint = 
  case instances of
    [] -> Nothing
    (inst:rest) -> 
      if instClass inst == constraint
      then Just inst
      else findMatchingInstance rest constraint

-- | Generate instance resolution code
generateInstanceResolution :: ResolutionContext -> T.Text
generateInstanceResolution ctx = T.unlines
  [ "// Type class instance resolution"
  , T.unlines $ Map.foldMapWithKey generateResolvedInstance (resolved ctx)
  ]

-- | Generate code for resolved instance
generateResolvedInstance :: T.Text -> TypeClassInstance -> T.Text
generateResolvedInstance className inst = T.unlines
  [ "// Instance for " <> className
  , "template<>"
  , "struct " <> className <> "_Instance<" <> T.intercalate ", " (instTypes inst) <> "> {"
  , T.unlines $ Map.foldMapWithKey generateMethodImpl (instMethods inst)
  , "};"
  ]

-- | Generate method implementation
generateMethodImpl :: T.Text -> T.Text -> T.Text
generateMethodImpl name impl = 
  "  static auto " <> name <> "() { return " <> impl <> "; }"

-- | Instance selection algorithm (simplified)
selectInstance :: [TypeClassInstance] -> [T.Text] -> Maybe TypeClassInstance
selectInstance instances types = 
  case filter (matchesTypes types) instances of
    [] -> Nothing
    [inst] -> Just inst
    (inst:_) -> Just inst  -- Take first match (simplified)

-- | Check if instance matches types
matchesTypes :: [T.Text] -> TypeClassInstance -> Bool
matchesTypes types inst = 
  length types == length (instTypes inst) &&
  all (\(t1, t2) -> t1 == t2) (zip types (instTypes inst))

-- | Constraint solving
solveConstraints :: [T.Text] -> Map.Map T.Text [TypeClassInstance] -> Either T.Text (Map.Map T.Text TypeClassInstance)
solveConstraints constraints' instances = 
  let ctx = ResolutionContext instances constraints' Map.empty
  in case resolveInstances ctx constraints' of
    Right resolvedCtx -> Right (resolved resolvedCtx)
    Left err -> Left err

-- | Generate constraint checking code
generateConstraintCheck :: T.Text -> [T.Text] -> T.Text
generateConstraintCheck className typeParams = T.unlines
  [ "template<" <> T.intercalate ", " (map (\p -> "typename " <> p) typeParams) <> ">"
  , "requires " <> T.intercalate " && " (map (\c -> c <> "<" <> T.intercalate ", " typeParams <> ">") [className])
  , "struct " <> className <> "_Constraint {"
  , "  static constexpr bool satisfied = true;"
  , "};"
  ]
