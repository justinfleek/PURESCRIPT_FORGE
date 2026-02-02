{-# LANGUAGE OverloadedStrings #-}
-- Phase 8: Dead Code Elimination
module DeadCodeElimination where

import qualified Data.Text as T
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Parser

-- | Eliminate dead code from module
eliminateDeadCode :: PSModule -> PSModule
eliminateDeadCode module'@PSModule{..} =
  let used = findUsedDeclarations moduleDeclarations moduleExports
      live = filter (\decl -> Set.member (declarationName decl) used) moduleDeclarations
  in module' { moduleDeclarations = live }

-- | Find all used declarations (reachability analysis)
findUsedDeclarations :: [PSDeclaration] -> [T.Text] -> Set.Set T.Text
findUsedDeclarations decls exports =
  let entryPoints = findEntryPoints decls exports
      dependencies = buildDependencyGraph decls
      reachable = reachableFrom entryPoints dependencies
  in reachable

-- | Find entry points (exported or main functions)
findEntryPoints :: [PSDeclaration] -> [T.Text] -> Set.Set T.Text
findEntryPoints decls exports =
  let mainFunc = filter (\d -> declarationName d == "main") decls
      exported = filter (\d -> declarationName d `elem` exports) decls
  in Set.fromList (map declarationName (mainFunc ++ exported))

-- | Build dependency graph
buildDependencyGraph :: [PSDeclaration] -> Map.Map T.Text (Set.Set T.Text)
buildDependencyGraph decls =
  Map.fromList $ map (\decl -> (declarationName decl, getDependencies decl)) decls

-- | Get dependencies of a declaration
getDependencies :: PSDeclaration -> Set.Set T.Text
getDependencies (PSValueDecl decl) = getNamesFromExpr (valueExpression decl)
getDependencies _ = Set.empty

-- | Find all names used in expression
getNamesFromExpr :: PSExpression -> Set.Set T.Text
getNamesFromExpr (PSVar name) = Set.singleton name
getNamesFromExpr (PSCon _) = Set.empty
getNamesFromExpr (PSLit _) = Set.empty
getNamesFromExpr (PSApp f x) = Set.union (getNamesFromExpr f) (getNamesFromExpr x)
getNamesFromExpr (PSAbs _ body) = getNamesFromExpr body
getNamesFromExpr (PSLet bindings body) =
  Set.union (Set.unions (map (getNamesFromExpr . snd) bindings)) (getNamesFromExpr body)
getNamesFromExpr (PSCase expr alts) =
  Set.union (getNamesFromExpr expr) (Set.unions (map (getNamesFromExpr . caseExpression) alts))
getNamesFromExpr (PSIf cond thenExpr elseExpr) =
  Set.unions [getNamesFromExpr cond, getNamesFromExpr thenExpr, getNamesFromExpr elseExpr]
getNamesFromExpr (PSDo stmts) = Set.unions (map getNamesFromStmt stmts)
getNamesFromExpr (PSRecord fields) = Set.unions (map (getNamesFromExpr . snd) fields)
getNamesFromExpr (PSRecordAccess expr _) = getNamesFromExpr expr
getNamesFromExpr (PSRecordUpdate expr fields) =
  Set.union (getNamesFromExpr expr) (Set.unions (map (getNamesFromExpr . snd) fields))

-- | Get names from statement
getNamesFromStmt :: PSStatement -> Set.Set T.Text
getNamesFromStmt (PSStmtBind _ expr) = getNamesFromExpr expr
getNamesFromStmt (PSStmtExpr expr) = getNamesFromExpr expr
getNamesFromStmt (PSStmtLet bindings) = Set.unions (map (getNamesFromExpr . snd) bindings)

-- | Find all reachable declarations from entry points
reachableFrom :: Set.Set T.Text -> Map.Map T.Text (Set.Set T.Text) -> Set.Set T.Text
reachableFrom entryPoints dependencies =
  let worklist = Set.toList entryPoints
      visited = Set.empty
      result = reachableFrom' worklist visited dependencies Set.empty
  in result

reachableFrom' :: [T.Text] -> Set.Set T.Text -> Map.Map T.Text (Set.Set T.Text) -> Set.Set T.Text -> Set.Set T.Text
reachableFrom' [] visited _ result = result
reachableFrom' (current:rest) visited deps result =
  if Set.member current visited
    then reachableFrom' rest visited deps result
    else
      let newVisited = Set.insert current visited
          newResult = Set.insert current result
          deps_current = Map.findWithDefault Set.empty current deps
          newWorklist = rest ++ Set.toList deps_current
      in reachableFrom' newWorklist newVisited deps newResult

-- | Get declaration name
declarationName :: PSDeclaration -> T.Text
declarationName (PSValueDecl decl) = valueName decl
declarationName (PSDataDecl decl) = dataName decl
declarationName (PSTypeDecl decl) = typeName decl
declarationName (PSClassDecl decl) = className decl
declarationName (PSInstanceDecl _) = ""  -- Instances don't have names
