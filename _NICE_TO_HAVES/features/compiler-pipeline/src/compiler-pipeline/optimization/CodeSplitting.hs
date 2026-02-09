{-# LANGUAGE OverloadedStrings #-}
-- Phase 8: Code Splitting
module CodeSplitting where

import qualified Data.Text as T
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Parser

-- | Split module into chunks for code splitting
splitModule :: PSModule -> Int -> [PSModule]
splitModule module'@PSModule{..} chunkSize =
  let chunks = splitIntoChunks moduleDeclarations chunkSize
  in map (\chunk -> module' { moduleDeclarations = chunk }) chunks

-- | Split declarations into chunks
splitIntoChunks :: [PSDeclaration] -> Int -> [[PSDeclaration]]
splitIntoChunks [] _ = []
splitIntoChunks decls size =
  let (chunk, rest) = splitAt size decls
  in chunk : splitIntoChunks rest size

-- | Split by dependency graph (more intelligent splitting)
splitByDependencies :: PSModule -> [PSModule]
splitByDependencies module'@PSModule{..} =
  let dependencyGraph = buildDependencyGraph moduleDeclarations
      stronglyConnected = findStronglyConnectedComponents dependencyGraph
      chunks = map (\scc -> filter (\decl -> Set.member (declarationName decl) scc) moduleDeclarations) stronglyConnected
  in map (\chunk -> module' { moduleDeclarations = chunk }) chunks

-- | Build dependency graph
buildDependencyGraph :: [PSDeclaration] -> Map.Map T.Text (Set.Set T.Text)
buildDependencyGraph decls =
  Map.fromList $ map (\decl -> (declarationName decl, getDependencies decl)) decls

-- | Get dependencies
getDependencies :: PSDeclaration -> Set.Set T.Text
getDependencies (PSValueDecl decl) = getNamesFromExpr (valueExpression decl)
getDependencies _ = Set.empty

-- | Find strongly connected components (simplified)
findStronglyConnectedComponents :: Map.Map T.Text (Set.Set T.Text) -> [Set.Set T.Text]
findStronglyConnectedComponents graph =
  -- Simplified: each node is its own component
  map Set.singleton (Map.keys graph)

-- | Get names from expression
getNamesFromExpr :: PSExpression -> Set.Set T.Text
getNamesFromExpr (PSVar name) = Set.singleton name
getNamesFromExpr (PSApp f x) = Set.union (getNamesFromExpr f) (getNamesFromExpr x)
getNamesFromExpr (PSAbs _ body) = getNamesFromExpr body
getNamesFromExpr (PSLet bindings body) =
  Set.union (Set.unions (map (getNamesFromExpr . snd) bindings)) (getNamesFromExpr body)
getNamesFromExpr (PSCase expr alts) =
  Set.union (getNamesFromExpr expr) (Set.unions (map (getNamesFromExpr . caseExpression) alts))
getNamesFromExpr _ = Set.empty

-- | Get declaration name
declarationName :: PSDeclaration -> T.Text
declarationName (PSValueDecl decl) = valueName decl
declarationName (PSDataDecl decl) = dataName decl
declarationName (PSTypeDecl decl) = typeName decl
declarationName (PSClassDecl decl) = className decl
declarationName (PSInstanceDecl _) = ""  -- Instances don't have names
