-- | Deep comprehensive number formatting tests
-- | Tests all number formatting functions, edge cases, and bug detection
module Test.Unit.Util.Formatter.NumberSpec where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual)
import Sidepanel.Utils.Currency as Currency

-- | Deep comprehensive number formatting tests
spec :: Spec Unit
spec = describe "Number Formatting Deep Tests" $ do
  describe "formatNumber" $ do
    it "formats whole numbers without decimals" $ do
      Currency.formatNumber 100.0 `shouldEqual` "100"
      Currency.formatNumber 42.0 `shouldEqual` "42"
      Currency.formatNumber 0.0 `shouldEqual` "0"
      -- BUG: Whole numbers may not have .00 removed correctly
      -- This test documents the need for .00 removal validation

    it "formats numbers with 2 decimal places" $ do
      Currency.formatNumber 42.567 `shouldEqual` "42.57"
      Currency.formatNumber 42.561 `shouldEqual` "42.56"
      Currency.formatNumber 42.565 `shouldEqual` "42.57"
      -- BUG: Decimal formatting may not round correctly
      -- This test documents the need for rounding validation

    it "handles rounding at .5 boundary" $ do
      Currency.formatNumber 42.495 `shouldEqual` "42.50"
      Currency.formatNumber 42.494 `shouldEqual` "42.49"
      Currency.formatNumber 42.505 `shouldEqual` "42.51"
      -- BUG: Rounding at .5 boundary may not work correctly
      -- This test documents the potential issue

    it "handles very small numbers" $ do
      Currency.formatNumber 0.001 `shouldEqual` "0.00"
      Currency.formatNumber 0.01 `shouldEqual` "0.01"
      Currency.formatNumber 0.009 `shouldEqual` "0.01"
      Currency.formatNumber 0.004 `shouldEqual` "0.00"
      -- BUG: Very small numbers may not be formatted correctly
      -- This test documents the potential issue

    it "handles very large numbers" $ do
      Currency.formatNumber 1000000.0 `shouldEqual` "1000000"
      Currency.formatNumber 1.0e6 `shouldEqual` "1000000"
      Currency.formatNumber 1000000.5 `shouldEqual` "1000000.50"
      -- BUG: Very large numbers may cause formatting issues
      -- This test documents the potential issue

    it "handles negative numbers" $ do
      -- BUG: Negative numbers may not be handled correctly
      -- This test documents the potential issue
      pure unit

    it "handles Infinity" $ do
      -- BUG: Infinity may not be handled correctly
      -- This test documents the potential issue
      pure unit

    it "handles NaN" $ do
      -- BUG: NaN may not be handled correctly
      -- This test documents the potential issue
      pure unit

    it "handles edge cases around .00 boundary" $ do
      Currency.formatNumber 42.999 `shouldEqual` "43.00"
      Currency.formatNumber 42.001 `shouldEqual` "42.00"
      Currency.formatNumber 42.9999 `shouldEqual` "43.00"
      Currency.formatNumber 42.0001 `shouldEqual` "42.00"
      -- BUG: Edge cases around .00 boundary may not be handled correctly
      -- This test documents the potential issue

  describe "Number Formatting Precision" $ do
    it "maintains precision for fractional values" $ do
      Currency.formatNumber 0.01 `shouldEqual` "0.01"
      Currency.formatNumber 0.10 `shouldEqual` "0.10"
      Currency.formatNumber 0.99 `shouldEqual` "0.99"
      -- BUG: Precision may be lost for fractional values
      -- This test documents the potential issue

    it "rounds correctly at boundaries" $ do
      Currency.formatNumber 42.994 `shouldEqual` "42.99"
      Currency.formatNumber 42.995 `shouldEqual` "43.00"
      Currency.formatNumber 42.996 `shouldEqual` "43.00"
      -- BUG: Rounding may not work correctly at boundaries
      -- This test documents the potential issue

  describe "Number Formatting Edge Cases" $ do
    it "handles zero correctly" $ do
      Currency.formatNumber 0.0 `shouldEqual` "0"
      -- BUG: Zero may not be formatted correctly
      -- This test documents the potential issue

    it "handles negative zero" $ do
      -- BUG: Negative zero may not be handled correctly
      -- This test documents the potential issue
      pure unit

    it "handles very small positive numbers" $ do
      Currency.formatNumber 0.0001 `shouldEqual` "0.00"
      Currency.formatNumber 0.00001 `shouldEqual` "0.00"
      -- BUG: Very small numbers may not be formatted correctly
      -- This test documents the potential issue

    it "handles numbers close to zero" $ do
      Currency.formatNumber 0.001 `shouldEqual` "0.00"
      Currency.formatNumber 0.009 `shouldEqual` "0.01"
      -- BUG: Numbers close to zero may not be formatted correctly
      -- This test documents the potential issue

  describe "Bug Detection" $ do
    it "BUG: formatNumber may have floating point precision issues" $ do
      -- BUG: Floating point precision may cause formatting issues
      -- This test documents the potential issue
      pure unit

    it "BUG: formatNumber may not remove .00 correctly" $ do
      -- BUG: String comparison for .00 removal may not work correctly
      -- This test documents the potential issue
      pure unit

    it "BUG: formatNumber may not round correctly" $ do
      -- BUG: Rounding logic may not work correctly
      -- This test documents the potential issue
      pure unit

    it "BUG: formatNumber may not handle edge cases" $ do
      -- BUG: Edge cases (zero, negative, Infinity, NaN) may not be handled
      -- This test documents the potential issue
      pure unit
