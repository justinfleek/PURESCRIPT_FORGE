{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
module Parser where

import qualified Data.Text as T
import qualified Data.ByteString as BS
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- | PureScript AST representation
data PSModule = PSModule
  { moduleName :: T.Text
  , moduleExports :: [T.Text]
  , moduleImports :: [PSImport]
  , moduleDeclarations :: [PSDeclaration]
  }

data PSImport = PSImport
  { importModule :: T.Text
  , importQualified :: Bool
  , importAs :: Maybe T.Text
  , importItems :: Maybe [T.Text]
  }

data PSDeclaration
  = PSDataDecl PSDataDeclaration
  | PSTypeDecl PSTypeDeclaration
  | PSValueDecl PSValueDeclaration
  | PSClassDecl PSClassDeclaration
  | PSInstanceDecl PSInstanceDeclaration
  deriving (Show, Eq)

data PSDataDeclaration = PSDataDeclaration
  { dataName :: T.Text
  , dataTypeVars :: [T.Text]
  , dataConstructors :: [PSConstructor]
  }
  deriving (Show, Eq)

data PSConstructor = PSConstructor
  { constructorName :: T.Text
  , constructorArgs :: [PSType]
  }
  deriving (Show, Eq)

data PSTypeDeclaration = PSTypeDeclaration
  { typeName :: T.Text
  , typeVars :: [T.Text]
  , typeDefinition :: PSType
  }
  deriving (Show, Eq)

data PSValueDeclaration = PSValueDeclaration
  { valueName :: T.Text
  , valueType :: Maybe PSType
  , valueExpression :: PSExpression
  }
  deriving (Show, Eq)

data PSClassDeclaration = PSClassDeclaration
  { className :: T.Text
  , classVars :: [T.Text]
  , classConstraints :: [PSConstraint]
  , classMembers :: [PSClassMember]
  }
  deriving (Show, Eq)

data PSInstanceDeclaration = PSInstanceDeclaration
  { instanceClass :: T.Text
  , instanceType :: PSType
  , instanceConstraints :: [PSConstraint]
  , instanceMembers :: [PSInstanceMember]
  }
  deriving (Show, Eq)

data PSConstraint = PSConstraint
  { constraintClass :: T.Text
  , constraintTypes :: [PSType]
  }
  deriving (Show, Eq)

data PSClassMember = PSClassMember
  { memberName :: T.Text
  , memberType :: PSType
  }
  deriving (Show, Eq)

data PSInstanceMember = PSInstanceMember
  { instanceMemberName :: T.Text
  , instanceMemberExpression :: PSExpression
  }
  deriving (Show, Eq)

data PSType
  = PSTypeVar T.Text
  | PSTypeCon T.Text [PSType]
  | PSTypeApp PSType PSType
  | PSTypeArr PSType PSType
  | PSTypeRecord [(T.Text, PSType)]
  | PSTypeRow [(T.Text, PSType)]
  deriving (Show, Eq)

data PSExpression
  = PSVar T.Text
  | PSCon T.Text
  | PSLit PSLiteral
  | PSApp PSExpression PSExpression
  | PSAbs [T.Text] PSExpression
  | PSLet [(T.Text, PSExpression)] PSExpression
  | PSCase PSExpression [PSCaseAlternative]
  | PSIf PSExpression PSExpression PSExpression
  | PSDo [PSStatement]
  | PSRecord [(T.Text, PSExpression)]
  | PSRecordAccess PSExpression T.Text
  | PSRecordUpdate PSExpression [(T.Text, PSExpression)]
  deriving (Show, Eq)

data PSLiteral
  = PSLitInt Integer
  | PSLitNumber Double
  | PSLitString T.Text
  | PSLitBoolean Bool
  | PSLitArray [PSExpression]
  deriving (Show, Eq)

data PSCaseAlternative = PSCaseAlternative
  { casePattern :: PSPattern
  , caseGuards :: [PSGuard]
  , caseExpression :: PSExpression
  }
  deriving (Show, Eq)

data PSPattern
  = PSPatVar T.Text
  | PSPatCon T.Text [PSPattern]
  | PSPatLit PSLiteral
  | PSPatWildcard
  | PSPatRecord [(T.Text, PSPattern)]
  deriving (Show, Eq)

data PSGuard = PSGuard
  { guardCondition :: PSExpression
  , guardExpression :: PSExpression
  }
  deriving (Show, Eq)

data PSStatement
  = PSStmtBind PSPattern PSExpression
  | PSStmtExpr PSExpression
  | PSStmtLet [(T.Text, PSExpression)]
  deriving (Show, Eq)

-- | Parse PureScript module
parseModule :: T.Text -> Either (ParseErrorBundle T.Text Void) PSModule
parseModule = parse (moduleParser <* eof) ""

moduleParser :: Parsec Void T.Text PSModule
moduleParser = do
  _ <- string "module"
  name <- identifier
  _ <- symbol "where"
  exports <- optional $ try (symbol "(" *> many identifier <* symbol ")")
  imports <- many importParser
  declarations <- many declarationParser
  pure $ PSModule name (maybe [] id exports) imports declarations

importParser :: Parsec Void T.Text PSImport
importParser = do
  _ <- string "import"
  qualified <- optional (string "qualified")
  moduleName' <- identifier
  as <- optional (string "as" *> identifier)
  items <- optional (symbol "(" *> many identifier <* symbol ")")
  _ <- symbol ";"
  pure $ PSImport moduleName' (isJust qualified) as items

declarationParser :: Parsec Void T.Text PSDeclaration
declarationParser = try dataDecl <|> try typeDecl <|> try valueDecl <|> try classDecl <|> instanceDecl

dataDecl :: Parsec Void T.Text PSDeclaration
dataDecl = do
  _ <- string "data"
  name <- identifier
  vars <- many identifier
  _ <- symbol "="
  constructors <- sepBy1 constructorParser (symbol "|")
  _ <- symbol ";"
  pure $ PSDataDecl $ PSDataDeclaration name vars constructors

constructorParser :: Parsec Void T.Text PSConstructor
constructorParser = do
  name <- identifier
  args <- many typeParser
  pure $ PSConstructor name args

typeDecl :: Parsec Void T.Text PSDeclaration
typeDecl = do
  _ <- string "type"
  name <- identifier
  vars <- many identifier
  _ <- symbol "="
  def <- typeParser
  _ <- symbol ";"
  pure $ PSTypeDecl $ PSTypeDeclaration name vars def

valueDecl :: Parsec Void T.Text PSDeclaration
valueDecl = do
  name <- identifier
  typ <- optional (symbol "::" *> typeParser)
  _ <- symbol "="
  expr <- expressionParser
  _ <- symbol ";"
  pure $ PSValueDecl $ PSValueDeclaration name typ expr

classDecl :: Parsec Void T.Text PSDeclaration
classDecl = do
  _ <- string "class"
  constraints <- optional (try (many constraintParser <* symbol "=>"))
  name <- identifier
  vars <- many identifier
  _ <- symbol "where"
  members <- many classMemberParser
  _ <- symbol ";"
  pure $ PSClassDecl $ PSClassDeclaration name vars (maybe [] id constraints) members

instanceDecl :: Parsec Void T.Text PSDeclaration
instanceDecl = do
  _ <- string "instance"
  constraints <- optional (try (many constraintParser <* symbol "=>"))
  className' <- identifier
  typ <- typeParser
  _ <- symbol "where"
  members <- many instanceMemberParser
  _ <- symbol ";"
  pure $ PSInstanceDecl $ PSInstanceDeclaration className' typ (maybe [] id constraints) members

constraintParser :: Parsec Void T.Text PSConstraint
constraintParser = do
  class' <- identifier
  types <- many typeParser
  pure $ PSConstraint class' types

classMemberParser :: Parsec Void T.Text PSClassMember
classMemberParser = do
  name <- identifier
  _ <- symbol "::"
  typ <- typeParser
  _ <- symbol ";"
  pure $ PSClassMember name typ

instanceMemberParser :: Parsec Void T.Text PSInstanceMember
instanceMemberParser = do
  name <- identifier
  _ <- symbol "="
  expr <- expressionParser
  _ <- symbol ";"
  pure $ PSInstanceMember name expr

typeParser :: Parsec Void T.Text PSType
typeParser = try arrType <|> try appType <|> try recordType <|> try rowType <|> conType <|> varType

varType :: Parsec Void T.Text PSType
varType = PSTypeVar <$> identifier

conType :: Parsec Void T.Text PSType
conType = PSTypeCon <$> identifier <*> pure []

appType :: Parsec Void T.Text PSType
appType = do
  con <- identifier
  args <- many1 (try typeParser)
  pure $ foldl PSTypeApp (PSTypeCon con []) args

arrType :: Parsec Void T.Text PSType
arrType = do
  left <- typeParser
  _ <- symbol "->"
  right <- typeParser
  pure $ PSTypeArr left right

recordType :: Parsec Void T.Text PSType
recordType = do
  _ <- symbol "{"
  fields <- sepBy fieldParser (symbol ",")
  _ <- symbol "}"
  pure $ PSTypeRecord fields

fieldParser :: Parsec Void T.Text (T.Text, PSType)
fieldParser = do
  name <- identifier
  _ <- symbol "::"
  typ <- typeParser
  pure (name, typ)

rowType :: Parsec Void T.Text PSType
rowType = do
  _ <- symbol "("
  fields <- sepBy fieldParser (symbol ",")
  _ <- symbol ")"
  pure $ PSTypeRow fields

expressionParser :: Parsec Void T.Text PSExpression
expressionParser = try doExpr <|> try caseExpr <|> try ifExpr <|> try letExpr <|> try absExpr <|> try appExpr <|> try recordExpr <|> try litExpr <|> varExpr

varExpr :: Parsec Void T.Text PSExpression
varExpr = PSVar <$> identifier

litExpr :: Parsec Void T.Text PSExpression
litExpr = PSLit <$> literalParser

literalParser :: Parsec Void T.Text PSLiteral
literalParser = try intLit <|> try numLit <|> try strLit <|> try boolLit <|> arrayLit

intLit :: Parsec Void T.Text PSLiteral
intLit = PSLitInt <$> L.decimal

numLit :: Parsec Void T.Text PSLiteral
numLit = PSLitNumber <$> L.float

strLit :: Parsec Void T.Text PSLiteral
strLit = PSLitString <$> (char '"' *> manyTill L.charLiteral (char '"'))

boolLit :: Parsec Void T.Text PSLiteral
boolLit = (PSLitBoolean True <$ string "true") <|> (PSLitBoolean False <$ string "false")

arrayLit :: Parsec Void T.Text PSLiteral
arrayLit = do
  _ <- symbol "["
  elems <- sepBy expressionParser (symbol ",")
  _ <- symbol "]"
  pure $ PSLitArray elems

appExpr :: Parsec Void T.Text PSExpression
appExpr = do
  func <- expressionParser
  arg <- expressionParser
  pure $ PSApp func arg

absExpr :: Parsec Void T.Text PSExpression
absExpr = do
  _ <- symbol "\\"
  params <- many1 identifier
  _ <- symbol "->"
  body <- expressionParser
  pure $ PSAbs params body

letExpr :: Parsec Void T.Text PSExpression
letExpr = do
  _ <- string "let"
  bindings <- many1 bindingParser
  _ <- string "in"
  body <- expressionParser
  pure $ PSLet bindings body

bindingParser :: Parsec Void T.Text (T.Text, PSExpression)
bindingParser = do
  name <- identifier
  _ <- symbol "="
  expr <- expressionParser
  _ <- symbol ";"
  pure (name, expr)

caseExpr :: Parsec Void T.Text PSExpression
caseExpr = do
  _ <- string "case"
  expr <- expressionParser
  _ <- string "of"
  alts <- many1 caseAltParser
  pure $ PSCase expr alts

caseAltParser :: Parsec Void T.Text PSCaseAlternative
caseAltParser = do
  pat <- patternParser
  guards <- many guardParser
  _ <- symbol "->"
  expr <- expressionParser
  _ <- symbol ";"
  pure $ PSCaseAlternative pat guards expr

guardParser :: Parsec Void T.Text PSGuard
guardParser = do
  _ <- symbol "|"
  cond <- expressionParser
  _ <- symbol "->"
  expr <- expressionParser
  pure $ PSGuard cond expr

ifExpr :: Parsec Void T.Text PSExpression
ifExpr = do
  _ <- string "if"
  cond <- expressionParser
  _ <- string "then"
  thenExpr <- expressionParser
  _ <- string "else"
  elseExpr <- expressionParser
  pure $ PSIf cond thenExpr elseExpr

doExpr :: Parsec Void T.Text PSExpression
doExpr = do
  _ <- string "do"
  stmts <- many1 statementParser
  pure $ PSDo stmts

statementParser :: Parsec Void T.Text PSStatement
statementParser = try bindStmt <|> try letStmt <|> exprStmt

bindStmt :: Parsec Void T.Text PSStatement
bindStmt = do
  pat <- patternParser
  _ <- symbol "<-"
  expr <- expressionParser
  _ <- symbol ";"
  pure $ PSStmtBind pat expr

letStmt :: Parsec Void T.Text PSStatement
letStmt = do
  _ <- string "let"
  bindings <- many1 bindingParser
  pure $ PSStmtLet bindings

exprStmt :: Parsec Void T.Text PSStatement
exprStmt = do
  expr <- expressionParser
  _ <- symbol ";"
  pure $ PSStmtExpr expr

recordExpr :: Parsec Void T.Text PSExpression
recordExpr = do
  _ <- symbol "{"
  fields <- sepBy recordFieldParser (symbol ",")
  _ <- symbol "}"
  pure $ PSRecord fields

recordFieldParser :: Parsec Void T.Text (T.Text, PSExpression)
recordFieldParser = do
  name <- identifier
  _ <- symbol "="
  expr <- expressionParser
  pure (name, expr)

patternParser :: Parsec Void T.Text PSPattern
patternParser = try conPat <|> try litPat <|> try recordPat <|> wildPat <|> varPat

varPat :: Parsec Void T.Text PSPattern
varPat = PSPatVar <$> identifier

wildPat :: Parsec Void T.Text PSPattern
wildPat = PSPatWildcard <$ symbol "_"

conPat :: Parsec Void T.Text PSPattern
conPat = do
  con <- identifier
  args <- many patternParser
  pure $ PSPatCon con args

litPat :: Parsec Void T.Text PSPattern
litPat = PSPatLit <$> literalParser

recordPat :: Parsec Void T.Text PSPattern
recordPat = do
  _ <- symbol "{"
  fields <- sepBy recordFieldPatParser (symbol ",")
  _ <- symbol "}"
  pure $ PSPatRecord fields

recordFieldPatParser :: Parsec Void T.Text (T.Text, PSPattern)
recordFieldPatParser = do
  name <- identifier
  _ <- symbol "="
  pat <- patternParser
  pure (name, pat)

-- Lexer helpers
sc :: Parsec Void T.Text ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parsec Void T.Text a -> Parsec Void T.Text a
lexeme = L.lexeme sc

symbol :: T.Text -> Parsec Void T.Text T.Text
symbol = L.symbol sc

identifier :: Parsec Void T.Text T.Text
identifier = lexeme $ T.pack <$> ((:) <$> letterChar <*> many (alphaNumChar <|> char '_' <|> char '\''))
