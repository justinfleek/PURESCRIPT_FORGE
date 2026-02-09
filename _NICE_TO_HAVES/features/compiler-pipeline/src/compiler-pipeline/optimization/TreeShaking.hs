{-# LANGUAGE OverloadedStrings #-}
-- Phase 8: Tree Shaking
module TreeShaking where

import qualified Data.Text as T
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Parser

-- | Tree shake module (remove unused exports)
treeShakeModule :: PSModule -> Set.Set T.Text -> PSModule
treeShakeModule module'@PSModule{..} usedExports =
  let filtered = filter (\decl -> isUsedExport decl usedExports moduleExports) moduleDeclarations
  in module' { moduleDeclarations = filtered }

-- | Check if declaration is a used export
isUsedExport :: PSDeclaration -> Set.Set T.Text -> [T.Text] -> Bool
isUsedExport decl usedExports exports =
  if declarationName decl `elem` exports
    then Set.member (declarationName decl) usedExports
    else True  -- Keep non-exported declarations (they might be used internally)

-- | Check if declaration is in exports list
isExported :: PSDeclaration -> [T.Text] -> Bool
isExported decl exports = declarationName decl `elem` exports

-- | Get declaration name
declarationName :: PSDeclaration -> T.Text
declarationName (PSValueDecl decl) = valueName decl
declarationName _ = ""
