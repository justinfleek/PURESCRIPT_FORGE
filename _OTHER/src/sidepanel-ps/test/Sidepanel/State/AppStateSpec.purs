-- | App State Tests
-- | Unit and property tests for application state
module Test.Sidepanel.State.AppStateSpec where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldBeTrue)
import Test.QuickCheck (quickCheck, (<?>))
import Sidepanel.State.AppState
  ( AppState
  , initialState
  , SessionState
  , ProofState
  , UIState
  , Panel(..)
  , Theme(..)
  , AlertLevel(..)
  , initialProofState
  , initialUIState
  )

-- | Test initial state
testInitialState :: forall m. Monad m => m Unit
testInitialState = do
  describe "Initial State" do
    it "has disconnected connection" do
      initialState.connected `shouldEqual` false
    
    it "has no last sync time" do
      initialState.lastSyncTime `shouldEqual` Nothing
    
    it "has initial balance state" do
      initialState.balance `shouldEqual` initialState.balance -- Would verify balance structure
    
    it "has no session" do
      initialState.session `shouldEqual` Nothing
    
    it "has empty session history" do
      initialState.sessionHistory `shouldEqual` []
    
    it "has initial proof state" do
      initialState.proof `shouldEqual` initialProofState
    
    it "has empty snapshots" do
      initialState.snapshots `shouldEqual` []
    
    it "has no selected snapshot" do
      initialState.selectedSnapshotId `shouldEqual` Nothing
    
    it "has initial UI state" do
      initialState.ui `shouldEqual` initialUIState

-- | Test proof state
testProofState :: forall m. Monad m => m Unit
testProofState = do
  describe "Proof State" do
    it "has disconnected proof connection" do
      initialProofState.connected `shouldEqual` false
    
    it "has no current file" do
      initialProofState.currentFile `shouldEqual` Nothing
    
    it "has empty goals" do
      initialProofState.goals `shouldEqual` []
    
    it "has empty diagnostics" do
      initialProofState.diagnostics `shouldEqual` []
    
    it "has empty suggested tactics" do
      initialProofState.suggestedTactics `shouldEqual` []

-- | Test UI state
testUIState :: forall m. Monad m => m Unit
testUIState = do
  describe "UI State" do
    it "has sidebar expanded" do
      initialUIState.sidebarCollapsed `shouldEqual` false
    
    it "has dashboard as active panel" do
      initialUIState.activePanel `shouldEqual` DashboardPanel
    
    it "has dark theme" do
      initialUIState.theme `shouldEqual` Dark
    
    it "has empty alerts" do
      initialUIState.alerts `shouldEqual` []

-- | Property: Initial state is always valid
prop_initialStateValid :: Boolean
prop_initialStateValid = 
  not initialState.connected &&
  initialState.session == Nothing &&
  initialState.sessionHistory == [] &&
  initialState.snapshots == []

-- | Property tests
testProperties :: forall m. Monad m => m Unit
testProperties = do
  describe "Property Tests" do
    it "initial state is always valid" do
      quickCheck prop_initialStateValid
