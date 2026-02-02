-- | Router Tests
-- | Unit and property tests for routing functionality
module Test.Sidepanel.RouterSpec where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldBeTrue)
import Test.QuickCheck (quickCheck, (<?>))
import Data.Maybe (Maybe(..))
import Sidepanel.Router (Route(..), parseRoute, printRoute, routeToPanel)
import Sidepanel.State.AppState (Panel(..))

-- | Test route parsing
testRouteParsing :: forall m. Monad m => m Unit
testRouteParsing = do
  describe "Route Parsing" do
    it "parses dashboard route" do
      parseRoute "/" `shouldEqual` Dashboard
    
    it "parses session route without ID" do
      parseRoute "/session" `shouldEqual` Session Nothing
    
    it "parses session route with ID" do
      parseRoute "/session?id=test-123" `shouldEqual` Session (Just "test-123")
    
    it "parses proof route" do
      parseRoute "/proof" `shouldEqual` Proof
    
    it "parses timeline route" do
      parseRoute "/timeline" `shouldEqual` Timeline
    
    it "parses settings route" do
      parseRoute "/settings" `shouldEqual` Settings
    
    it "parses terminal route" do
      parseRoute "/terminal" `shouldEqual` Terminal
    
    it "parses file context route" do
      parseRoute "/file-context" `shouldEqual` FileContext
    
    it "parses diff viewer route" do
      parseRoute "/diff" `shouldEqual` DiffViewer
    
    it "parses invalid route as NotFound" do
      parseRoute "/invalid" `shouldEqual` NotFound

-- | Test route printing
testRoutePrinting :: forall m. Monad m => m Unit
testRoutePrinting = do
  describe "Route Printing" do
    it "prints dashboard route" do
      printRoute Dashboard `shouldEqual` "/"
    
    it "prints session route without ID" do
      printRoute (Session Nothing) `shouldEqual` "/session"
    
    it "prints session route with ID" do
      printRoute (Session (Just "test-123")) `shouldEqual` "/session?id=test-123"
    
    it "prints proof route" do
      printRoute Proof `shouldEqual` "/proof"
    
    it "prints timeline route" do
      printRoute Timeline `shouldEqual` "/timeline"
    
    it "prints settings route" do
      printRoute Settings `shouldEqual` "/settings"
    
    it "prints terminal route" do
      printRoute Terminal `shouldEqual` "/terminal"
    
    it "prints file context route" do
      printRoute FileContext `shouldEqual` "/file-context"
    
    it "prints diff viewer route" do
      printRoute DiffViewer `shouldEqual` "/diff"

-- | Test route to panel mapping
testRouteToPanel :: forall m. Monad m => m Unit
testRouteToPanel = do
  describe "Route to Panel Mapping" do
    it "maps dashboard route to DashboardPanel" do
      routeToPanel Dashboard `shouldEqual` DashboardPanel
    
    it "maps session route to SessionPanel" do
      routeToPanel (Session Nothing) `shouldEqual` SessionPanel
      routeToPanel (Session (Just "test")) `shouldEqual` SessionPanel
    
    it "maps proof route to ProofPanel" do
      routeToPanel Proof `shouldEqual` ProofPanel
    
    it "maps timeline route to TimelinePanel" do
      routeToPanel Timeline `shouldEqual` TimelinePanel
    
    it "maps settings route to SettingsPanel" do
      routeToPanel Settings `shouldEqual` SettingsPanel
    
    it "maps terminal route to TerminalPanel" do
      routeToPanel Terminal `shouldEqual` TerminalPanel
    
    it "maps file context route to FileContextPanel" do
      routeToPanel FileContext `shouldEqual` FileContextPanel
    
    it "maps diff viewer route to DiffViewerPanel" do
      routeToPanel DiffViewer `shouldEqual` DiffViewerPanel
    
    it "maps NotFound route to DashboardPanel" do
      routeToPanel NotFound `shouldEqual` DashboardPanel

-- | Property: Route parsing and printing are inverse operations
prop_routeRoundTrip :: Route -> Boolean
prop_routeRoundTrip route = 
  parseRoute (printRoute route) == route

-- | Property: Route to panel mapping is total
prop_routeToPanelTotal :: Route -> Boolean
prop_routeToPanelTotal route = 
  case routeToPanel route of
    DashboardPanel -> true
    SessionPanel -> true
    ProofPanel -> true
    TimelinePanel -> true
    SettingsPanel -> true
    TerminalPanel -> true
    FileContextPanel -> true
    DiffViewerPanel -> true

-- | Property tests
testProperties :: forall m. Monad m => m Unit
testProperties = do
  describe "Property Tests" do
    it "route parsing and printing are inverse" do
      quickCheck prop_routeRoundTrip
    
    it "route to panel mapping is total" do
      quickCheck prop_routeToPanelTotal
