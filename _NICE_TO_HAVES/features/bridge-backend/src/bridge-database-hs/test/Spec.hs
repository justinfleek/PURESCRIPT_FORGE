-- | Test Suite Entry Point
-- | Runs all database tests
module Main where

import Test.Hspec
import qualified Bridge.DatabaseSpec as DatabaseSpec
import qualified Bridge.DatabaseE2ESpec as DatabaseE2E
import qualified Bridge.DatabaseOperationsSpec as DatabaseOperationsSpec
import qualified Bridge.DatabaseSchemaSpec as DatabaseSchemaSpec
import qualified Bridge.Integration.BackupSpec as BackupIntegration
import qualified Bridge.Integration.SecuritySpec as SecurityIntegration

main :: IO ()
main = hspec $ do
  DatabaseSpec.spec
  DatabaseSpec.testInvariants
  DatabaseE2E.spec
  DatabaseE2E.testIntegrity
  DatabaseOperationsSpec.spec
  DatabaseSchemaSpec.spec
  BackupIntegration.spec
  SecurityIntegration.spec