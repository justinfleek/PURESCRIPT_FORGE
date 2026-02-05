{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
module Main where

import Data.Aeson
import Data.Aeson.Types
import Data.Text (Text, pack, unpack)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Vector (Vector)
import qualified Data.Vector as V
import System.Environment
import System.FilePath
import Control.Monad
import Data.Maybe
import Data.List (intercalate)

-- | OpenAPI Schema representation
data OpenAPISchema = OpenAPISchema
  { schemaType :: Maybe Text
  , schemaFormat :: Maybe Text
  , schemaRef :: Maybe Text
  , schemaItems :: Maybe OpenAPISchema
  , schemaProperties :: Maybe (HashMap Text OpenAPISchema)
  , schemaRequired :: Maybe (Vector Text)
  , schemaEnum :: Maybe (Vector Value)
  , schemaAllOf :: Maybe (Vector OpenAPISchema)
  , schemaOneOf :: Maybe (Vector OpenAPISchema)
  , schemaAnyOf :: Maybe (Vector OpenAPISchema)
  , schemaNullable :: Maybe Bool
  }

instance FromJSON OpenAPISchema where
  parseJSON = withObject "OpenAPISchema" $ \o -> OpenAPISchema
    <$> o .:? "type"
    <*> o .:? "format"
    <*> o .:? "$ref"
    <*> o .:? "items"
    <*> o .:? "properties"
    <*> o .:? "required"
    <*> o .:? "enum"
    <*> o .:? "allOf"
    <*> o .:? "oneOf"
    <*> o .:? "anyOf"
    <*> o .:? "nullable"

-- | Generate PureScript type from OpenAPI schema
generatePSType :: Text -> OpenAPISchema -> Text
generatePSType name schema
  | Just ref <- schemaRef schema = generateRefType ref
  | Just (Just "array") <- fmap schemaType (schemaItems schema) = "Array " <> generatePSType name (fromMaybe (OpenAPISchema Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing) (schemaItems schema))
  | Just "array" <- schemaType schema = case schemaItems schema of
      Just items -> "Array " <> generatePSType name items
      Nothing -> "Array Json"
  | Just "object" <- schemaType schema = generateObjectType name schema
  | Just "string" <- schemaType schema = "String"
  | Just "integer" <- schemaType schema = "Int"
  | Just "number" <- schemaType schema = "Number"
  | Just "boolean" <- schemaType schema = "Boolean"
  | Just enumValues <- schemaEnum schema = generateEnumType name enumValues
  | otherwise = "Json"

generateRefType :: Text -> Text
generateRefType ref = T.replace "#/components/schemas/" "" ref

generateObjectType :: Text -> OpenAPISchema -> Text
generateObjectType name schema = case schemaProperties schema of
  Just props -> "{\n  " <> T.intercalate "\n  " (map generateProperty (HM.toList props)) <> "\n}"
  Nothing -> "Json"
  where
    required = maybe [] V.toList (schemaRequired schema)
    generateProperty (propName, propSchema) =
      let propType = generatePSType propName propSchema
          isRequired = propName `elem` required
          optional = if isRequired then "" else "Maybe "
      in T.unpack propName <> " :: " <> optional <> T.unpack propType

generateEnumType :: Text -> Vector Value -> Text
generateEnumType name values = "String" -- Simplified: use String for enums

-- | Generate PureScript module
generatePSModule :: Text -> [Text] -> Text -> Text
generatePSModule moduleName imports content =
  "-- | Auto-generated from OpenAPI spec\n"
  <> "module " <> moduleName <> " where\n\n"
  <> T.intercalate "\n" (map (\i -> "import " <> i) imports) <> "\n\n"
  <> content

main :: IO ()
main = do
  args <- getArgs
  case args of
    [inputFile, outputDir] -> do
      json <- eitherDecodeFileStrict inputFile
      case json of
        Left err -> putStrLn $ "Error parsing JSON: " <> err
        Right spec -> generateSDK spec outputDir
    _ -> putStrLn "Usage: codegen <openapi.json> <output-dir>"

generateSDK :: Value -> FilePath -> IO ()
generateSDK spec outputDir = do
  -- Extract components/schemas
  let schemas = extractSchemas spec
  -- Generate types module
  let typesContent = generateTypesModule schemas
  T.writeFile (outputDir </> "Types.purs") typesContent
  putStrLn $ "Generated " <> (outputDir </> "Types.purs")

extractSchemas :: Value -> HashMap Text OpenAPISchema
extractSchemas = fromMaybe HM.empty . parseMaybe (withObject "OpenAPI" $ \o ->
  o .: "components" >>= (.: "schemas"))

generateTypesModule :: HashMap Text OpenAPISchema -> Text
generateTypesModule schemas =
  generatePSModule "Opencode.SDK.Types"
    [ "Prelude"
    , "Data.Argonaut (Json)"
    , "Data.Maybe (Maybe)"
    , "Data.Array (Array)"
    ]
    (T.intercalate "\n\n" (map generateTypeDecl (HM.toList schemas)))
  where
    generateTypeDecl (name, schema) =
      "type " <> name <> " =\n  " <> generatePSType name schema
