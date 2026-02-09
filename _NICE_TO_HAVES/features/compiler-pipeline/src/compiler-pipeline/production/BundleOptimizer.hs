{-# LANGUAGE OverloadedStrings #-}
-- Phase 8: Bundle Size Optimization
module BundleOptimizer where

import qualified Data.Text as T
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import qualified Data.List as L
import Parser (PSModule(..), PSDeclaration(..), PSValueDeclaration(..),
               PSExpression(..), PSStatement(..))
import Cpp23Generator (generateCpp23Header, generateCpp23Impl)

-- | Optimize bundle size
optimizeBundleSize :: PSModule -> PSModule
optimizeBundleSize module' =
  let minified = minifyNames module'
      compressed = compressExpressions minified
      deduplicated = deduplicateCode compressed
  in deduplicated

-- | Minify names (shorten identifiers)
minifyNames :: PSModule -> PSModule
minifyNames module'@PSModule{..} =
  let nameMap = buildNameMap moduleDeclarations
      minified = map (minifyDeclaration nameMap) moduleDeclarations
  in module' { moduleDeclarations = minified }

-- | Build name mapping (short names)
buildNameMap :: [PSDeclaration] -> Map.Map T.Text T.Text
buildNameMap decls =
  let names = map declarationName decls
      shortNames = generateShortNames (length names)
  in Map.fromList (zip names shortNames)

-- | Generate short names (a, b, c, ..., aa, ab, ...)
generateShortNames :: Int -> [T.Text]
generateShortNames count = take count $ concatMap generateNamesForLength [1..]
  where
    generateNamesForLength len = map (T.pack . generateName len) [0..]
    generateName len idx = 
      let base = 26
          digits = reverse $ toBase base idx
          pad = replicate (len - length digits) 0
          allDigits = pad ++ digits
      in map (\d -> ['a'..'z'] !! d) allDigits

-- | Convert number to base
toBase :: Int -> Int -> [Int]
toBase base 0 = [0]
toBase base n = 
  let (q, r) = n `divMod` base
  in if q == 0 then [r] else toBase base q ++ [r]

-- | Minify declaration
minifyDeclaration :: Map.Map T.Text T.Text -> PSDeclaration -> PSDeclaration
minifyDeclaration nameMap (PSValueDecl decl) =
  let minifiedName = Map.findWithDefault (valueName decl) (valueName decl) nameMap
      minifiedExpr = minifyExpression nameMap (valueExpression decl)
  in PSValueDecl decl { valueName = minifiedName, valueExpression = minifiedExpr }
minifyDeclaration _ decl = decl

-- | Minify expression
minifyExpression :: Map.Map T.Text T.Text -> PSExpression -> PSExpression
minifyExpression nameMap (PSVar name) =
  PSVar (Map.findWithDefault name name nameMap)
minifyExpression nameMap (PSCon con) = PSCon con
minifyExpression nameMap (PSLit lit) = PSLit lit
minifyExpression nameMap (PSApp f x) =
  PSApp (minifyExpression nameMap f) (minifyExpression nameMap x)
minifyExpression nameMap (PSAbs params body) =
  PSAbs params (minifyExpression nameMap body)
minifyExpression nameMap (PSLet bindings body) =
  PSLet (map (\(n, e) -> (Map.findWithDefault n n nameMap, minifyExpression nameMap e)) bindings)
        (minifyExpression nameMap body)
minifyExpression nameMap (PSCase expr alts) =
  PSCase (minifyExpression nameMap expr)
         (map (\alt -> alt { caseExpression = minifyExpression nameMap (caseExpression alt) }) alts)
minifyExpression nameMap (PSIf cond thenExpr elseExpr) =
  PSIf (minifyExpression nameMap cond) 
       (minifyExpression nameMap thenExpr) 
       (minifyExpression nameMap elseExpr)
minifyExpression nameMap (PSDo stmts) =
  PSDo (map (minifyStatement nameMap) stmts)
minifyExpression nameMap (PSRecord fields) =
  PSRecord (map (\(n, e) -> (n, minifyExpression nameMap e)) fields)
minifyExpression nameMap (PSRecordAccess expr field) =
  PSRecordAccess (minifyExpression nameMap expr) field
minifyExpression nameMap (PSRecordUpdate expr fields) =
  PSRecordUpdate (minifyExpression nameMap expr) 
                 (map (\(n, e) -> (n, minifyExpression nameMap e)) fields)

-- | Minify statement
minifyStatement :: Map.Map T.Text T.Text -> PSStatement -> PSStatement
minifyStatement nameMap (PSStmtBind pat expr) = PSStmtBind pat (minifyExpression nameMap expr)
minifyStatement nameMap (PSStmtExpr expr) = PSStmtExpr (minifyExpression nameMap expr)
minifyStatement nameMap (PSStmtLet bindings) =
  PSStmtLet (map (\(n, e) -> (Map.findWithDefault n n nameMap, minifyExpression nameMap e)) bindings)

-- | Compress expressions (remove whitespace, simplify)
compressExpressions :: PSModule -> PSModule
compressExpressions = id  -- Expression compression handled in generator

-- | Deduplicate code (extract common patterns)
deduplicateCode :: PSModule -> PSModule
deduplicateCode module'@PSModule{..} =
  let commonPatterns = findCommonPatterns moduleDeclarations
      extracted = extractCommonPatterns commonPatterns moduleDeclarations
  in module' { moduleDeclarations = extracted }

-- | Find common patterns (expressions that appear multiple times)
findCommonPatterns :: [PSDeclaration] -> [PSExpression]
findCommonPatterns decls =
  let allExprs = concatMap getAllExpressions decls
      exprCounts = countExpressions allExprs
      common = filter (\(expr, count) -> count > 1 && expressionSize expr > 5) exprCounts
  in map fst (take 10 (L.sortBy (\a b -> compare (snd b) (snd a)) common))

-- | Get all expressions from declaration
getAllExpressions :: PSDeclaration -> [PSExpression]
getAllExpressions (PSValueDecl decl) = collectExpressions (valueExpression decl)
getAllExpressions _ = []

-- | Collect all sub-expressions
collectExpressions :: PSExpression -> [PSExpression]
collectExpressions expr@(PSApp f x) = expr : collectExpressions f ++ collectExpressions x
collectExpressions expr@(PSAbs _ body) = expr : collectExpressions body
collectExpressions expr@(PSLet bindings body) = expr : concatMap (collectExpressions . snd) bindings ++ collectExpressions body
collectExpressions expr@(PSCase e alts) = expr : collectExpressions e ++ concatMap (collectExpressions . caseExpression) alts
collectExpressions expr@(PSIf c t e) = expr : collectExpressions c ++ collectExpressions t ++ collectExpressions e
collectExpressions expr@(PSDo stmts) = expr : concatMap (collectExpressions . getStmtExpr) stmts
collectExpressions expr@(PSRecord fields) = expr : concatMap (collectExpressions . snd) fields
collectExpressions expr@(PSRecordAccess e _) = expr : collectExpressions e
collectExpressions expr@(PSRecordUpdate e fields) = expr : collectExpressions e ++ concatMap (collectExpressions . snd) fields
collectExpressions expr = [expr]

-- | Get expression from statement
getStmtExpr :: PSStatement -> PSExpression
getStmtExpr (PSStmtBind _ expr) = expr
getStmtExpr (PSStmtExpr expr) = expr
getStmtExpr (PSStmtLet bindings) = PSLet bindings (PSVar "_")  -- Dummy expression

-- | Count expression occurrences
countExpressions :: [PSExpression] -> [(PSExpression, Int)]
countExpressions exprs =
  let grouped = L.group (L.sort exprs)
  in map (\group -> (head group, length group)) grouped

-- | Calculate expression size (approximate)
expressionSize :: PSExpression -> Int
expressionSize (PSVar _) = 1
expressionSize (PSCon _) = 1
expressionSize (PSLit _) = 1
expressionSize (PSApp f x) = 1 + expressionSize f + expressionSize x
expressionSize (PSAbs _ body) = 1 + expressionSize body
expressionSize (PSLet bindings body) = 1 + sum (map (expressionSize . snd) bindings) + expressionSize body
expressionSize (PSCase expr alts) = 1 + expressionSize expr + sum (map (expressionSize . caseExpression) alts)
expressionSize (PSIf cond thenExpr elseExpr) = 1 + expressionSize cond + expressionSize thenExpr + expressionSize elseExpr
expressionSize (PSDo stmts) = 1 + sum (map (expressionSize . getStmtExpr) stmts)
expressionSize (PSRecord fields) = 1 + sum (map (expressionSize . snd) fields)
expressionSize (PSRecordAccess expr _) = 1 + expressionSize expr
expressionSize (PSRecordUpdate expr fields) = 1 + expressionSize expr + sum (map (expressionSize . snd) fields)

-- | Extract common patterns into shared functions
extractCommonPatterns :: [PSExpression] -> [PSDeclaration] -> [PSDeclaration]
extractCommonPatterns patterns decls =
  if null patterns
    then decls
    else
      let pattern = head patterns
          patternName = "extracted_" <> T.pack (show (hashExpression pattern))
          extractedDecl = PSValueDecl PSValueDeclaration
            { valueName = patternName
            , valueType = Nothing
            , valueExpression = pattern
            }
          replaced = map (replaceExpression pattern (PSVar patternName)) decls
      in extractedDecl : extractCommonPatterns (tail patterns) replaced

-- | Hash expression for naming
hashExpression :: PSExpression -> Int
hashExpression = foldl (\acc c -> acc * 31 + fromEnum c) 0 . T.unpack . T.pack . show

-- | Replace expression occurrences
replaceExpression :: PSExpression -> PSExpression -> PSDeclaration -> PSDeclaration
replaceExpression old new (PSValueDecl decl) =
  PSValueDecl decl { valueExpression = replaceInExpression old new (valueExpression decl) }
replaceExpression _ _ decl = decl

-- | Replace expression in expression tree
replaceInExpression :: PSExpression -> PSExpression -> PSExpression -> PSExpression
replaceInExpression old new expr
  | expr == old = new
  | otherwise = case expr of
      PSApp f x -> PSApp (replaceInExpression old new f) (replaceInExpression old new x)
      PSAbs params body -> PSAbs params (replaceInExpression old new body)
      PSLet bindings body -> PSLet (map (\(n, e) -> (n, replaceInExpression old new e)) bindings)
                                   (replaceInExpression old new body)
      PSCase e alts -> PSCase (replaceInExpression old new e)
                              (map (\alt -> alt { caseExpression = replaceInExpression old new (caseExpression alt) }) alts)
      PSIf c t e -> PSIf (replaceInExpression old new c)
                         (replaceInExpression old new t)
                         (replaceInExpression old new e)
      PSDo stmts -> PSDo (map (replaceInStatement old new) stmts)
      PSRecord fields -> PSRecord (map (\(n, e) -> (n, replaceInExpression old new e)) fields)
      PSRecordAccess e field -> PSRecordAccess (replaceInExpression old new e) field
      PSRecordUpdate e fields -> PSRecordUpdate (replaceInExpression old new e)
                                                (map (\(n, e') -> (n, replaceInExpression old new e')) fields)
      _ -> expr

-- | Replace in statement
replaceInStatement :: PSExpression -> PSExpression -> PSStatement -> PSStatement
replaceInStatement old new (PSStmtBind pat expr) = PSStmtBind pat (replaceInExpression old new expr)
replaceInStatement old new (PSStmtExpr expr) = PSStmtExpr (replaceInExpression old new expr)
replaceInStatement old new (PSStmtLet bindings) =
  PSStmtLet (map (\(n, e) -> (n, replaceInExpression old new e)) bindings)

-- | Get declaration name
declarationName :: PSDeclaration -> T.Text
declarationName (PSValueDecl decl) = valueName decl
declarationName (PSDataDecl decl) = dataName decl
declarationName (PSTypeDecl decl) = typeName decl
declarationName (PSClassDecl decl) = className decl
declarationName (PSInstanceDecl _) = ""

-- | Estimate bundle size
estimateBundleSize :: PSModule -> Int
estimateBundleSize module' =
  let header = generateCpp23Header module'
      impl = generateCpp23Impl module'
  in T.length header + T.length impl
