{-|
Module      : Sidepanel.Components.ErrorAnalysis.ErrorAnalysis
Description : Main Halogen component for error analysis
Main component that provides error analysis and debugging assistance.
-}
module Sidepanel.Components.ErrorAnalysis.ErrorAnalysis where

import Prelude

import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Effect.Aff (Aff)
import Sidepanel.Components.ErrorAnalysis.ErrorAnalysisTypes
  ( ErrorAnalysis
  , Error
  )
import Sidepanel.Components.ErrorAnalysis.ErrorAnalyzer (analyzeError)
import Sidepanel.Components.ErrorAnalysis.StackTraceParser (parseStackTrace)

-- | Component state
type State =
  { currentError :: Maybe Error
  , analysis :: Maybe ErrorAnalysis
  , loading :: Boolean
  }

-- | Component query
data Query a
  = AnalyzeError Error a
  | ClearAnalysis a

-- | Component slot
type Slot = H.Slot Query Void

-- | Component name
component :: forall i m. H.Component Query i Void m
component =
  H.mkComponent
    { initialState: \_ -> { currentError: Nothing, analysis: Nothing, loading: false }
    , render
    , eval: H.mkEval $ H.defaultEval
        { handleQuery = handleQuery
        }
    }

-- | Handle queries
handleQuery :: forall a m. Query a -> H.HalogenM State Query Void m (Maybe a)
handleQuery = case _ of
  AnalyzeError error a -> do
    H.modify_ _ { loading = true, currentError = Just error }
    -- Parse stack trace if present
    let error' = case error.stackTrace of
          Nothing -> error
          Just _ -> error { stackTrace = Just (parseStackTrace (fromMaybe "" (error.stackTrace >>= _.raw))) }
    
    -- Analyze error
    analysis <- H.lift $ analyzeError error'
    H.modify_ _ { analysis = Just analysis, loading = false }
    pure (Just a)
  
  ClearAnalysis a -> do
    H.modify_ _ { currentError = Nothing, analysis = Nothing }
    pure (Just a)

-- | Render component
render :: State -> H.ComponentHTML Query Void m
render state =
  HH.div
    [ HP.class_ (HH.ClassName "error-analysis") ]
    [ HH.h2_ [ HH.text "Error Analysis" ]
    , case state.analysis of
        Nothing ->
          if state.loading then
            HH.div_ [ HH.text "Analyzing error..." ]
          else
            HH.div_ [ HH.text "No error to analyze" ]
        Just analysis ->
          HH.div_
            [ HH.h3_ [ HH.text "Error Explanation" ]
            , HH.p_ [ HH.text analysis.explanation ]
            , HH.h3_ [ HH.text "Root Cause" ]
            , case analysis.rootCause of
                Nothing -> HH.p_ [ HH.text "Unable to determine root cause" ]
                Just loc -> HH.p_
                    [ HH.text ("Location: " <> loc.file <> ":" <> show loc.line <> ":" <> show loc.column)
                    ]
            , HH.h3_ [ HH.text "Fix Suggestions" ]
            , HH.ul_ $ Array.map (\suggestion ->
                HH.li_
                  [ HH.text (suggestion.description <> " (" <> show (suggestion.confidence * 100.0) <> "% confidence)")
                  , HH.p_ [ HH.text suggestion.explanation ]
                  ]
              ) analysis.suggestions
            , HH.h3_ [ HH.text "Debugging Steps" ]
            , HH.ol_ $ Array.map (\step ->
                HH.li_ [ HH.text step ]
              ) analysis.debuggingSteps
            ]
    ]
