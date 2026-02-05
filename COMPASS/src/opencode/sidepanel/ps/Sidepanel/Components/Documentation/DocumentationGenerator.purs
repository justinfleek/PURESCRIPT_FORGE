{-|
Module      : Sidepanel.Components.Documentation.DocumentationGenerator
Description : Generate documentation from code
Generates function documentation, API docs, README, and code comments.
-}
module Sidepanel.Components.Documentation.DocumentationGenerator where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)
import Sidepanel.Components.Documentation.DocumentationTypes
  ( Documentation
  , DocumentationType(..)
  , FunctionDoc
  , APIDoc
  , READMEDoc
  , Comment
  , CodeElement(..)
  , CodeContext
  )

-- | Generate documentation for code element
generateDocumentation :: CodeElement -> CodeContext -> DocumentationType -> Aff Documentation
generateDocumentation element context docType = case docType of
  FunctionDocumentation -> generateFunctionDoc element context
  APIDocumentation -> generateAPIDoc element context
  READMEDocumentation -> generateREADMEDoc element context
  CommentDocumentation -> generateComments element context
  ArchitectureDocumentation -> generateArchitectureDoc element context

-- | Generate function documentation
generateFunctionDoc :: CodeElement -> CodeContext -> Aff Documentation
generateFunctionDoc element context = do
  case element of
    FunctionElement func -> do
      let doc = analyzeFunction func context
      pure
        { type_: FunctionDocumentation
        , content: formatFunctionDoc doc
        , metadata: { language: context.language, file: context.file }
        }
    _ -> pure
      { type_: FunctionDocumentation
      , content: ""
      , metadata: { language: context.language, file: context.file }
      }

-- | Analyze function to generate documentation
analyzeFunction :: { name :: String, signature :: String, body :: String, parameters :: Array String } -> CodeContext -> FunctionDoc
analyzeFunction func context =
  { name: func.name
  , signature: func.signature
  , description: inferDescription func.name func.body
  , parameters: Array.map (\param -> { name: param, description: inferParameterDescription param func.body, type_: Nothing }) func.parameters
  , returnType: extractReturnType func.signature
  , returnDescription: inferReturnDescription func.body
  , examples: generateExamples func context
  , throws: detectExceptions func.body
  , seeAlso: findRelatedFunctions func.name context
  }

-- | Infer function description from name and body
inferDescription :: String -> String -> String
inferDescription name body =
  -- Extract key operations from function body
  let operations = extractOperations body
      description = if String.length operations > 0 then
            name <> " " <> operations
          else
            "Function " <> name
  in
    description

-- | Extract operations from function body
extractOperations :: String -> String
extractOperations body =
  -- Simplified: look for common patterns
  if String.contains (String.Pattern "return") body then
    "returns a value"
  else if String.contains (String.Pattern "throw") body then
    "may throw an error"
  else if String.contains (String.Pattern "async") body then
    "performs an asynchronous operation"
  else
    "performs operations"

-- | Infer parameter description
inferParameterDescription :: String -> String -> String
inferParameterDescription paramName body =
  -- Look for usage of parameter in body
  if String.contains (String.Pattern paramName) body then
    "The " <> paramName <> " parameter"
  else
    "Parameter " <> paramName

-- | Extract return type from signature
extractReturnType :: String -> Maybe String
extractReturnType signature =
  -- Look for return type annotation
  if String.contains (String.Pattern "->") signature then
    let parts = String.split (String.Pattern "->") signature
        returnPart = Array.last parts
    in
      returnPart
  else
    Nothing

-- | Infer return description
inferReturnDescription :: String -> String
inferReturnDescription body =
  if String.contains (String.Pattern "return") body then
    "Returns the computed result"
  else
    "Returns a value"

-- | Generate examples
generateExamples :: { name :: String, signature :: String, body :: String, parameters :: Array String } -> CodeContext -> Array String
generateExamples func context =
  -- Generate example usage
  [ func.name <> "(" <> String.joinWith ", " (Array.map (\p -> "example" <> p) func.parameters) <> ")" ]

-- | Detect exceptions
detectExceptions :: String -> Array String
detectExceptions body =
  -- Look for throw statements
  if String.contains (String.Pattern "throw") body then
    ["May throw an exception"]
  else
    []

-- | Find related functions
findRelatedFunctions :: String -> CodeContext -> Array String
findRelatedFunctions functionName context =
  -- Would search context for related functions
  []

-- | Format function documentation
formatFunctionDoc :: FunctionDoc -> String
formatFunctionDoc doc =
  "## " <> doc.name <> "\n\n" <>
  doc.description <> "\n\n" <>
  "### Signature\n\n" <>
  "```" <> (if String.contains (String.Pattern "::") doc.signature then "purescript" else "typescript") <> "\n" <>
  doc.signature <> "\n" <>
  "```\n\n" <>
  formatParameters doc.parameters <>
  formatReturnType doc.returnType doc.returnDescription <>
  formatExamples doc.examples <>
  formatThrows doc.throws <>
  formatSeeAlso doc.seeAlso

-- | Format parameters
formatParameters :: Array { name :: String, description :: String, type_ :: Maybe String } -> String
formatParameters params =
  if Array.length params == 0 then
    ""
  else
    "### Parameters\n\n" <>
    String.joinWith "\n" (Array.map (\p ->
      "- **" <> p.name <> "**: " <> p.description <>
      (case p.type_ of
        Nothing -> ""
        Just t -> " (" <> t <> ")")
    ) params) <> "\n\n"

-- | Format return type
formatReturnType :: Maybe String -> String -> String
formatReturnType returnTypeM returnDesc =
  case returnTypeM of
    Nothing -> ""
    Just returnType ->
      "### Returns\n\n" <>
      "**" <> returnType <> "**: " <> returnDesc <> "\n\n"

-- | Format examples
formatExamples :: Array String -> String
formatExamples examples =
  if Array.length examples == 0 then
    ""
  else
    "### Examples\n\n" <>
    String.joinWith "\n\n" (Array.map (\ex -> "```\n" <> ex <> "\n```") examples) <> "\n\n"

-- | Format throws
formatThrows :: Array String -> String
formatThrows throws =
  if Array.length throws == 0 then
    ""
  else
    "### Throws\n\n" <>
    String.joinWith "\n" (Array.map (\t -> "- " <> t) throws) <> "\n\n"

-- | Format see also
formatSeeAlso :: Array String -> String
formatSeeAlso seeAlso =
  if Array.length seeAlso == 0 then
    ""
  else
    "### See Also\n\n" <>
    String.joinWith ", " seeAlso <> "\n\n"

-- | Generate API documentation
generateAPIDoc :: CodeElement -> CodeContext -> Aff Documentation
generateAPIDoc element context = do
  let apiDoc = buildAPIDoc element context
  pure
    { type_: APIDocumentation
    , content: formatAPIDoc apiDoc
    , metadata: { language: context.language, file: context.file }
    }

-- | Build API documentation
buildAPIDoc :: CodeElement -> CodeContext -> APIDoc
buildAPIDoc element context =
  { title: extractTitle element
  , description: extractDescription element context
  , endpoints: extractEndpoints element
  , types: extractTypes element
  , examples: extractAPIExamples element context
  }

-- | Extract title
extractTitle :: CodeElement -> String
extractTitle = case _ of
  FunctionElement func -> func.name
  ModuleElement name -> name
  ClassElement name -> name
  _ -> "API Documentation"

-- | Extract description
extractDescription :: CodeElement -> CodeContext -> String
extractDescription element context =
  "API documentation for " <> extractTitle element

-- | Extract endpoints
extractEndpoints :: CodeElement -> Array { method :: String, path :: String, description :: String }
extractEndpoints = case _ of
  FunctionElement func -> []
  ModuleElement _ -> []
  ClassElement _ -> []
  _ -> []

-- | Extract types
extractTypes :: CodeElement -> Array { name :: String, definition :: String }
extractTypes = case _ of
  FunctionElement func -> []
  ModuleElement _ -> []
  ClassElement _ -> []
  _ -> []

-- | Extract API examples
extractAPIExamples :: CodeElement -> CodeContext -> Array String
extractAPIExamples element context = []

-- | Format API documentation
formatAPIDoc :: APIDoc -> String
formatAPIDoc doc =
  "# " <> doc.title <> "\n\n" <>
  doc.description <> "\n\n" <>
  formatEndpoints doc.endpoints <>
  formatTypes doc.types <>
  formatAPIExamples doc.examples

-- | Format endpoints
formatEndpoints :: Array { method :: String, path :: String, description :: String } -> String
formatEndpoints endpoints =
  if Array.length endpoints == 0 then
    ""
  else
    "## Endpoints\n\n" <>
    String.joinWith "\n\n" (Array.map (\ep ->
      "### " <> ep.method <> " " <> ep.path <> "\n\n" <>
      ep.description
    ) endpoints) <> "\n\n"

-- | Format types
formatTypes :: Array { name :: String, definition :: String } -> String
formatTypes types =
  if Array.length types == 0 then
    ""
  else
    "## Types\n\n" <>
    String.joinWith "\n\n" (Array.map (\t ->
      "### " <> t.name <> "\n\n" <>
      "```\n" <> t.definition <> "\n```"
    ) types) <> "\n\n"

-- | Format API examples
formatAPIExamples :: Array String -> String
formatAPIExamples examples =
  if Array.length examples == 0 then
    ""
  else
    "## Examples\n\n" <>
    String.joinWith "\n\n" examples <> "\n\n"

-- | Generate README documentation
generateREADMEDoc :: CodeElement -> CodeContext -> Aff Documentation
generateREADMEDoc element context = do
  let readmeDoc = buildREADMEDoc element context
  pure
    { type_: READMEDocumentation
    , content: formatREADMEDoc readmeDoc
    , metadata: { language: context.language, file: context.file }
    }

-- | Build README documentation
buildREADMEDoc :: CodeElement -> CodeContext -> READMEDoc
buildREADMEDoc element context =
  { title: extractProjectName context
  , description: extractProjectDescription context
  , installation: generateInstallation context
  , usage: generateUsage context
  , api: generateAPIOverview context
  , examples: generateUsageExamples context
  , contributing: generateContributing context
  , license: extractLicense context
  }

-- | Extract project name
extractProjectName :: CodeContext -> String
extractProjectName context =
  -- Would extract from package.json, spago.dhall, etc.
  "Project"

-- | Extract project description
extractProjectDescription :: CodeContext -> String
extractProjectDescription context =
  "A project built with " <> context.language

-- | Generate installation instructions
generateInstallation :: CodeContext -> String
generateInstallation context =
  case context.language of
    "purescript" -> "Install using Spago:\n\n```bash\nspago install\n```"
    "haskell" -> "Install using Cabal:\n\n```bash\ncabal build\n```"
    "typescript" -> "Install using npm:\n\n```bash\nnpm install\n```"
    _ -> "Install dependencies using your package manager"

-- | Generate usage
generateUsage :: CodeContext -> String
generateUsage context =
  "## Usage\n\n" <>
  "Import and use the module:\n\n" <>
  "```" <> context.language <> "\n" <>
  "import Module\n" <>
  "```"

-- | Generate API overview
generateAPIOverview :: CodeContext -> String
generateAPIOverview context =
  "## API\n\n" <>
  "See API documentation for details."

-- | Generate usage examples
generateUsageExamples :: CodeContext -> String
generateUsageExamples context =
  "## Examples\n\n" <>
  "See examples in the examples directory."

-- | Generate contributing
generateContributing :: CodeContext -> String
generateContributing context =
  "## Contributing\n\n" <>
  "Contributions welcome! Please read the contributing guidelines."

-- | Extract license
extractLicense :: CodeContext -> String
extractLicense context =
  "## License\n\n" <>
  "See LICENSE file for details."

-- | Format README documentation
formatREADMEDoc :: READMEDoc -> String
formatREADMEDoc doc =
  "# " <> doc.title <> "\n\n" <>
  doc.description <> "\n\n" <>
  "## Installation\n\n" <>
  doc.installation <> "\n\n" <>
  doc.usage <> "\n\n" <>
  doc.api <> "\n\n" <>
  doc.examples <> "\n\n" <>
  doc.contributing <> "\n\n" <>
  doc.license <> "\n\n"

-- | Generate comments
generateComments :: CodeElement -> CodeContext -> Aff Documentation
generateComments element context = do
  let comments = analyzeCodeForComments element context
  pure
    { type_: CommentDocumentation
    , content: formatComments comments
    , metadata: { language: context.language, file: context.file }
    }

-- | Analyze code for comment suggestions
analyzeCodeForComments :: CodeElement -> CodeContext -> Array Comment
analyzeCodeForComments element context = case element of
  FunctionElement func -> do
    let complexity = calculateComplexity func.body
    if complexity > 5 then
      [ { location: { file: context.file, line: 0, column: 0 }
        , text: "Complex function - consider adding inline comments explaining the algorithm"
        , priority: 1
        }
      ]
    else
      []
  _ -> []

-- | Calculate complexity
calculateComplexity :: String -> Int
calculateComplexity body =
  let ifCount = countOccurrences body "if"
      loopCount = countOccurrences body "for" + countOccurrences body "while"
      nestedCount = countOccurrences body "{{"
  in
    1 + ifCount + loopCount + nestedCount

-- | Count occurrences
countOccurrences :: String -> String -> Int
countOccurrences str substr =
  let pattern = String.Pattern substr
  in
    String.split pattern str # Array.length # (_ - 1)

-- | Format comments
formatComments :: Array Comment -> String
formatComments comments =
  String.joinWith "\n\n" (Array.map (\c ->
    "**" <> c.location.file <> ":" <> show c.location.line <> "**\n\n" <>
    c.text
  ) comments)

-- | Generate architecture documentation
generateArchitectureDoc :: CodeElement -> CodeContext -> Aff Documentation
generateArchitectureDoc element context = do
  let archDoc = buildArchitectureDoc element context
  pure
    { type_: ArchitectureDocumentation
    , content: formatArchitectureDoc archDoc
    , metadata: { language: context.language, file: context.file }
    }

-- | Build architecture documentation
buildArchitectureDoc :: CodeElement -> CodeContext -> { title :: String, components :: Array String, relationships :: Array String, diagrams :: Array String }
buildArchitectureDoc element context =
  { title: "Architecture Documentation"
  , components: extractComponents context
  , relationships: extractRelationships context
  , diagrams: generateDiagrams context
  }

-- | Extract components
extractComponents :: CodeContext -> Array String
extractComponents context = []

-- | Extract relationships
extractRelationships :: CodeContext -> Array String
extractRelationships context = []

-- | Generate diagrams
generateDiagrams :: CodeContext -> Array String
generateDiagrams context = []

-- | Format architecture documentation
formatArchitectureDoc :: { title :: String, components :: Array String, relationships :: Array String, diagrams :: Array String } -> String
formatArchitectureDoc doc =
  "# " <> doc.title <> "\n\n" <>
  "## Components\n\n" <>
  String.joinWith "\n" (Array.map (\c -> "- " <> c) doc.components) <> "\n\n" <>
  "## Relationships\n\n" <>
  String.joinWith "\n" (Array.map (\r -> "- " <> r) doc.relationships) <> "\n\n"
