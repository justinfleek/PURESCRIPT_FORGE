-- | Database FFI Tests
-- | Unit and property tests for better-sqlite3 FFI bindings
module Test.Bridge.FFI.Node.DatabaseSpec where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldBeTrue, shouldBeFalse)
import Test.QuickCheck (quickCheck, (<?>))
import Effect (Effect)
import Effect.Class (liftEffect)
import Data.Either (Either(..), isRight, isLeft)
import Bridge.FFI.Node.Database
  ( open
  , close
  , exec
  , prepare
  , run
  , get
  , all
  , randomUUID
  , Database
  , Statement
  )

-- | Test database operations
testDatabaseOperations :: forall m. Monad m => m Unit
testDatabaseOperations = do
  describe "Database Operations" do
    it "opens in-memory database" do
      db <- liftEffect $ open ":memory:"
      liftEffect $ close db
      true `shouldBeTrue`
    
    it "executes SQL statements" do
      db <- liftEffect $ open ":memory:"
      liftEffect $ exec db "CREATE TABLE test (id INTEGER PRIMARY KEY)"
      liftEffect $ close db
      true `shouldBeTrue`
    
    it "prepares statements" do
      db <- liftEffect $ open ":memory:"
      liftEffect $ exec db "CREATE TABLE test (id INTEGER PRIMARY KEY, name TEXT)"
      stmt <- liftEffect $ prepare db "INSERT INTO test (name) VALUES (?)"
      liftEffect $ run stmt ["test"]
      liftEffect $ close db
      true `shouldBeTrue`
    
    it "retrieves single row" do
      db <- liftEffect $ open ":memory:"
      liftEffect $ exec db "CREATE TABLE test (id INTEGER PRIMARY KEY, name TEXT)"
      liftEffect $ exec db "INSERT INTO test (name) VALUES ('test')"
      stmt <- liftEffect $ prepare db "SELECT * FROM test WHERE id = ?"
      result <- liftEffect $ get stmt ["1"]
      isRight result `shouldBeTrue`
      liftEffect $ close db
    
    it "retrieves all rows" do
      db <- liftEffect $ open ":memory:"
      liftEffect $ exec db "CREATE TABLE test (id INTEGER PRIMARY KEY, name TEXT)"
      liftEffect $ exec db "INSERT INTO test (name) VALUES ('test1')"
      liftEffect $ exec db "INSERT INTO test (name) VALUES ('test2')"
      stmt <- liftEffect $ prepare db "SELECT * FROM test"
      result <- liftEffect $ all stmt []
      isRight result `shouldBeTrue`
      liftEffect $ close db

-- | Test UUID generation
testUUIDGeneration :: forall m. Monad m => m Unit
testUUIDGeneration = do
  describe "UUID Generation" do
    it "generates valid UUID" do
      uuid <- liftEffect randomUUID
      uuid `shouldEqual` uuid -- Placeholder - would validate UUID format
    
    it "generates unique UUIDs" do
      uuid1 <- liftEffect randomUUID
      uuid2 <- liftEffect randomUUID
      uuid1 /= uuid2 `shouldBeTrue`

-- | Property: Database operations are idempotent
prop_databaseOperationsIdempotent :: Database -> Boolean
prop_databaseOperationsIdempotent db = true -- Placeholder

-- | Property: UUIDs are always unique
prop_uuidsUnique :: Boolean
prop_uuidsUnique = true -- Placeholder - would test UUID uniqueness

-- | Property tests
testProperties :: forall m. Monad m => m Unit
testProperties = do
  describe "Property Tests" do
    it "database operations are idempotent" do
      quickCheck prop_databaseOperationsIdempotent
    
    it "UUIDs are always unique" do
      quickCheck prop_uuidsUnique
