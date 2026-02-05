{-|
Module      : Test.Main
Description : Main test suite entry point
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

Orchestrates all property tests and integration tests.
-}
module Test.Main where

import Prelude

import Effect (Effect)
import Test.Spec (Spec)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (runSpec)

-- Import all test suites
import Tool.ASTEdit.Test.Structural.TransformSpec as TransformSpec
import Tool.ASTEdit.Test.Structural.IntegrationSpec as TransformIntegrationSpec
import Aleph.Sandbox.Test.GVisorSpec as GVisorSpec
import Aleph.Sandbox.Test.GVisorIntegrationSpec as GVisorIntegrationSpec
import Tool.Search.Test.SearXNGSpec as SearXNGSpec
import Tool.Search.Test.SearXNGIntegrationSpec as SearXNGIntegrationSpec

-- ============================================================================
-- MAIN TEST SUITE
-- ============================================================================

main :: Effect Unit
main = runSpec [consoleReporter] do
  describe "Property Tests" do
    TransformSpec.spec
    GVisorSpec.spec
    SearXNGSpec.spec
  
  describe "Integration Tests" do
    TransformIntegrationSpec.spec
    GVisorIntegrationSpec.spec
    SearXNGIntegrationSpec.spec
