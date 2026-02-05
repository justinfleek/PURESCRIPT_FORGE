{-|
Module      : Sidepanel.Components.SemanticCode.SemanticCode
Description : Main semantic code understanding component
Main component that provides semantic code understanding: symbol navigation,
cross-file awareness, dependency graphs, etc.
-}
module Sidepanel.Components.SemanticCode.SemanticCode where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Effect.Aff (Aff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes (Position)
import Sidepanel.Components.SemanticCode.LSPClient
  ( LSPConnection
  , SymbolInfo
  , Location
  , connectLSP
  , getSymbolAtPosition
  , goToDefinition
  , findReferences
  )
import Sidepanel.Components.SemanticCode.SemanticIndex
  ( SemanticIndex
  , buildSemanticIndex
  , findSymbol
  , findSymbolReferences
  )

-- | Component state
type State =
  { lspConnections :: Map.Map String LSPConnection
  , semanticIndex :: Maybe SemanticIndex
  , currentFile :: Maybe String
  , hoveredSymbol :: Maybe SymbolInfo
  }

-- | Component actions
data Action
  = Initialize
  | FileOpened String
  | HoverSymbol String Position
  | GoToDefinition String Position
  | FindReferences String Position
  | UpdateIndex String

-- | Component output
data Output
  = SymbolHovered SymbolInfo
  | DefinitionFound Location
  | ReferencesFound (Array Location)
  | IndexUpdated

-- | Component input
type Input = Unit

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \_ ->
      { lspConnections: Map.empty
      , semanticIndex: Nothing
      , currentFile: Nothing
      , hoveredSymbol: Nothing
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

-- | Render component
render :: forall m. State -> H.ComponentHTML Action () m
render state = do
  HH.div
    [ HP.class_ (H.ClassName "semantic-code") ]
    [ HH.div
        [ HP.class_ (H.ClassName "symbol-info") ]
        [ case state.hoveredSymbol of
            Nothing -> HH.text ""
            Just symbol -> renderSymbolInfo symbol
        ]
    ]

-- | Render symbol information
renderSymbolInfo :: forall m. SymbolInfo -> H.ComponentHTML Action () m
renderSymbolInfo symbol = do
  HH.div
    [ HP.class_ (H.ClassName "symbol-details") ]
    [ HH.h3_ [ HH.text symbol.name ]
    , case symbol.type_ of
        Nothing -> HH.text ""
        Just type_ -> HH.p [ HP.class_ (H.ClassName "symbol-type") ] [ HH.text type_ ]
    , case symbol.documentation of
        Nothing -> HH.text ""
        Just docs -> HH.p [ HP.class_ (H.ClassName "symbol-docs") ] [ HH.text docs ]
    ]

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Connect to LSP servers for supported languages
    -- Would connect to TypeScript, PureScript, Haskell, Lean4 LSP servers
    pure unit
  
  FileOpened filePath -> do
    H.modify_ _ { currentFile = Just filePath }
    handleAction (UpdateIndex filePath)
  
  HoverSymbol fileUri position -> do
    state <- H.get
    -- Get LSP connection for file language
    let language = detectLanguage fileUri
    case Map.lookup language state.lspConnections of
      Nothing -> pure unit
      Just connection -> do
        symbolInfo <- getSymbolAtPosition connection fileUri position
        case symbolInfo of
          Nothing -> pure unit
          Just symbol -> do
            H.modify_ _ { hoveredSymbol = Just symbol }
            H.raise (SymbolHovered symbol)
  
  GoToDefinition fileUri position -> do
    state <- H.get
    let language = detectLanguage fileUri
    case Map.lookup language state.lspConnections of
      Nothing -> pure unit
      Just connection -> do
        location <- goToDefinition connection fileUri position
        case location of
          Nothing -> pure unit
          Just loc -> do
            H.raise (DefinitionFound loc)
  
  FindReferences fileUri position -> do
    state <- H.get
    let language = detectLanguage fileUri
    case Map.lookup language state.lspConnections of
      Nothing -> pure unit
      Just connection -> do
        references <- findReferences connection fileUri position
        H.raise (ReferencesFound references)
  
  UpdateIndex filePath -> do
    state <- H.get
    -- Update semantic index for file
    case state.semanticIndex of
      Nothing -> do
        -- Build initial index
        index <- buildSemanticIndex [filePath]
        H.modify_ _ { semanticIndex = Just index }
      Just index -> do
        -- Update existing index
        updatedIndex <- updateIndexForFile index filePath
        H.modify_ _ { semanticIndex = Just updatedIndex }
    H.raise IndexUpdated

-- | Detect language from file path
detectLanguage :: String -> String
detectLanguage filePath = do
  if String.contains (String.Pattern ".ts") filePath then
    "typescript"
  else if String.contains (String.Pattern ".purs") filePath then
    "purescript"
  else if String.contains (String.Pattern ".hs") filePath then
    "haskell"
  else if String.contains (String.Pattern ".lean") filePath then
    "lean4"
  else
    "unknown"

-- | Import Map and updateIndexForFile
import Data.Map as Map
import Sidepanel.Components.SemanticCode.SemanticIndex (updateIndexForFile)
