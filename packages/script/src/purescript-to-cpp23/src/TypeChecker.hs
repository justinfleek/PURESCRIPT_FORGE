{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
module TypeChecker where

import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Parser

-- | Type environment for type checking
type TypeEnv = Map.Map T.Text PSType

-- | Type class environment
type ClassEnv = Map.Map T.Text PSClassDeclaration

-- | Type checking context
data TypeContext = TypeContext
  { typeEnv :: TypeEnv
  , classEnv :: ClassEnv
  , constraints :: [PSConstraint]
  }

-- | Type check a module
typeCheckModule :: PSModule -> Either T.Text PSModule
typeCheckModule module'@PSModule{..} = do
  -- Build class environment
  classPairs <- mapM (\d -> case d of
        PSClassDecl c -> Right (className c, c)
        _ -> Left "Not a class") moduleDeclarations
  let classEnv' = Map.fromList classPairs
  
  -- Build initial type environment
  typePairs <- mapM (\d -> case d of
        PSValueDecl v -> case valueType v of
          Just t -> Right (valueName v, t)
          Nothing -> Left "No type annotation"
        _ -> Left "Not a value") moduleDeclarations
  let typeEnv' = Map.fromList typePairs
  
  let ctx = TypeContext typeEnv' classEnv' []
  
  -- Type check each declaration
  checkedDecls <- mapM (typeCheckDeclaration ctx) moduleDeclarations
  
  return module' { moduleDeclarations = checkedDecls }

-- | Type check a declaration
typeCheckDeclaration :: TypeContext -> PSDeclaration -> Either T.Text PSDeclaration
typeCheckDeclaration ctx (PSValueDecl decl) = do
  -- Infer type if not provided
  inferredType <- case valueType decl of
    Just t -> return t
    Nothing -> inferType ctx (valueExpression decl)
  
  -- Check expression against type
  checkedExpr <- checkType ctx (valueExpression decl) inferredType
  
  return $ PSValueDecl decl
    { valueType = Just inferredType
    , valueExpression = checkedExpr
    }
typeCheckDeclaration ctx (PSDataDecl decl) = do
  -- Check data declaration
  return $ PSDataDecl decl
typeCheckDeclaration ctx (PSTypeDecl decl) = do
  -- Check type declaration
  return $ PSTypeDecl decl
typeCheckDeclaration ctx (PSClassDecl decl) = do
  -- Check class declaration
  return $ PSClassDecl decl
typeCheckDeclaration ctx (PSInstanceDecl decl) = do
  -- Check instance declaration
  return $ PSInstanceDecl decl

-- | Infer type of expression
inferType :: TypeContext -> PSExpression -> Either T.Text PSType
inferType ctx (PSVar v) = case Map.lookup v (typeEnv ctx) of
  Just t -> return t
  Nothing -> Left $ "Undefined variable: " <> v
inferType ctx (PSCon c) = 
  -- Look up constructor type
  return $ PSTypeCon c []
inferType ctx (PSLit (PSLitInt _)) = return $ PSTypeCon "Int" []
inferType ctx (PSLit (PSLitNumber _)) = return $ PSTypeCon "Number" []
inferType ctx (PSLit (PSLitString _)) = return $ PSTypeCon "String" []
inferType ctx (PSLit (PSLitBoolean _)) = return $ PSTypeCon "Boolean" []
inferType ctx (PSLit (PSLitArray elems)) = do
  elemTypes <- mapM (inferType ctx) elems
  -- All elements should have same type
  case elemTypes of
    [] -> return $ PSTypeCon "Array" [PSTypeVar "a"]
    (t:_) -> return $ PSTypeCon "Array" [t]
inferType ctx (PSApp f x) = do
  fType <- inferType ctx f
  xType <- inferType ctx x
  case fType of
    PSTypeArr argType retType -> do
      -- Unify argument types
      _ <- unifyTypes argType xType
      return retType
    _ -> Left "Type error: function application"
inferType ctx (PSAbs params body) = do
  -- Create new type variables for parameters
  paramTypes <- mapM (\_ -> return $ PSTypeVar "a") params
  -- Infer body type
  bodyType <- inferType (ctx { typeEnv = foldl (\env (p, t) -> Map.insert p t env) (typeEnv ctx) (zip params paramTypes) }) body
  -- Build function type
  return $ foldr PSTypeArr bodyType paramTypes
inferType ctx (PSLet bindings body) = do
  -- Type check bindings
  newCtx <- foldM (\c (name, expr) -> do
    exprType <- inferType c expr
    return $ c { typeEnv = Map.insert name exprType (typeEnv c) }
    ) ctx bindings
  -- Type check body
  inferType newCtx body
inferType ctx (PSCase scrut alts) = do
  scrutType <- inferType ctx scrut
  -- Infer types from alternatives
  altTypes <- mapM (\alt -> inferType ctx (caseExpression alt)) alts
  -- All alternatives should have same type
  case altTypes of
    [] -> Left "Empty case expression"
    (t:_) -> return t
inferType ctx (PSIf cond thenExpr elseExpr) = do
  condType <- inferType ctx cond
  _ <- checkType ctx cond (PSTypeCon "Boolean" [])
  thenType <- inferType ctx thenExpr
  elseType <- inferType ctx elseExpr
  _ <- unifyTypes thenType elseType
  return thenType
inferType ctx (PSDo stmts) = do
  -- Type check statements
  finalCtx <- foldM (\c stmt -> case stmt of
    PSStmtBind pat expr -> do
      exprType <- inferType c expr
      return $ c { typeEnv = Map.insert (patternToVar pat) exprType (typeEnv c) }
    PSStmtExpr expr -> do
      _ <- inferType c expr
      return c
    PSStmtLet bindings -> do
      newCtx <- foldM (\ctx' (name, expr) -> do
        exprType <- inferType ctx' expr
        return $ ctx' { typeEnv = Map.insert name exprType (typeEnv ctx') }
        ) c bindings
      return newCtx
    ) ctx stmts
  -- Return type of last statement
  case reverse stmts of
    [] -> Left "Empty do expression"
    (PSStmtExpr expr:_) -> inferType finalCtx expr
    (PSStmtBind _ expr:_) -> inferType finalCtx expr
    _ -> Left "Invalid do expression"
inferType ctx (PSRecord fields) = do
  fieldTypes <- mapM (\(name, expr) -> do
    exprType <- inferType ctx expr
    return (name, exprType)
    ) fields
  return $ PSTypeRecord fieldTypes
inferType ctx (PSRecordAccess rec field) = do
  recType <- inferType ctx rec
  case recType of
    PSTypeRecord fields -> case lookup field fields of
      Just t -> return t
      Nothing -> Left $ "Field not found: " <> field
    _ -> Left "Type error: record access"
inferType ctx (PSRecordUpdate rec fields) = do
  recType <- inferType ctx rec
  case recType of
    PSTypeRecord _ -> return recType
    _ -> Left "Type error: record update"

-- | Check expression against expected type
checkType :: TypeContext -> PSExpression -> PSType -> Either T.Text PSExpression
checkType ctx expr expectedType = do
  inferredType <- inferType ctx expr
  _ <- unifyTypes inferredType expectedType
  return expr

-- | Unify two types
unifyTypes :: PSType -> PSType -> Either T.Text ()
unifyTypes (PSTypeVar _) _ = return ()  -- Type variable unifies with anything
unifyTypes _ (PSTypeVar _) = return ()
unifyTypes (PSTypeCon n1 args1) (PSTypeCon n2 args2)
  | n1 == n2 && length args1 == length args2 = 
      mapM_ (uncurry unifyTypes) (zip args1 args2)
  | otherwise = Left $ "Type mismatch: " <> n1 <> " vs " <> n2
unifyTypes (PSTypeArr a1 b1) (PSTypeArr a2 b2) = do
  unifyTypes a1 a2
  unifyTypes b1 b2
unifyTypes (PSTypeRecord fields1) (PSTypeRecord fields2) = do
  -- Check all fields match
  mapM_ (\(name, t1) -> case lookup name fields2 of
    Just t2 -> unifyTypes t1 t2
    Nothing -> Left $ "Missing field: " <> name
    ) fields1
unifyTypes t1 t2 = Left $ "Cannot unify types"

patternToVar :: PSPattern -> T.Text
patternToVar (PSPatVar v) = v
patternToVar _ = "_"
