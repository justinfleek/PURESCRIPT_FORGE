-- | PRISM Theme Tests
-- | Unit and property tests for PRISM theme generation
module Test.Sidepanel.Theme.PrismSpec where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)
import Test.QuickCheck (quickCheck)
import Effect.Class (liftEffect)
import Data.String.CodeUnits (length, take) as SCU
import Sidepanel.Theme.Prism
  ( generateHolographicTheme
  , generateFleekTheme
  , fleekColors
  , MonitorType(..)
  )

-- | Check if a string is a valid 7-character hex color (#RRGGBB)
isValidHexColor :: String -> Boolean
isValidHexColor s = SCU.length s == 7 && SCU.take 1 s == "#"

-- | Test Fleek colors
testFleekColors :: Spec Unit
testFleekColors =
  describe "Fleek Colors" do
    it "defines Fleek blue" do
      fleekColors.fleekBlue `shouldEqual` "#0090ff"

    it "defines Fleek green" do
      fleekColors.fleekGreen `shouldEqual` "#32e48e"

    it "defines Fleek yellow" do
      fleekColors.fleekYellow `shouldEqual` "#ffe629"

    it "defines Fleek orange" do
      fleekColors.fleekOrange `shouldEqual` "#f76b15"

-- | Test Holographic theme generation
testHolographicTheme :: Spec Unit
testHolographicTheme =
  describe "Holographic Theme Generation" do
    it "generates theme for OLED monitor" do
      let theme = generateHolographicTheme OLED
      isValidHexColor theme.base00 `shouldSatisfy` identity
      isValidHexColor theme.base05 `shouldSatisfy` identity
      isValidHexColor theme.base0A `shouldSatisfy` identity

    it "generates theme for LCD monitor" do
      let theme = generateHolographicTheme LCD
      isValidHexColor theme.base00 `shouldSatisfy` identity
      isValidHexColor theme.base05 `shouldSatisfy` identity
      isValidHexColor theme.base0A `shouldSatisfy` identity

    it "generates all Base16 colors as valid hex" do
      let theme = generateHolographicTheme OLED
      isValidHexColor theme.base00 `shouldSatisfy` identity
      isValidHexColor theme.base01 `shouldSatisfy` identity
      isValidHexColor theme.base02 `shouldSatisfy` identity
      isValidHexColor theme.base03 `shouldSatisfy` identity
      isValidHexColor theme.base04 `shouldSatisfy` identity
      isValidHexColor theme.base05 `shouldSatisfy` identity
      isValidHexColor theme.base06 `shouldSatisfy` identity
      isValidHexColor theme.base07 `shouldSatisfy` identity
      isValidHexColor theme.base08 `shouldSatisfy` identity
      isValidHexColor theme.base09 `shouldSatisfy` identity
      isValidHexColor theme.base0A `shouldSatisfy` identity
      isValidHexColor theme.base0B `shouldSatisfy` identity
      isValidHexColor theme.base0C `shouldSatisfy` identity
      isValidHexColor theme.base0D `shouldSatisfy` identity
      isValidHexColor theme.base0E `shouldSatisfy` identity
      isValidHexColor theme.base0F `shouldSatisfy` identity

-- | Test Fleek theme generation
testFleekTheme :: Spec Unit
testFleekTheme =
  describe "Fleek Theme Generation" do
    it "generates theme for OLED monitor" do
      let theme = generateFleekTheme OLED
      isValidHexColor theme.base00 `shouldSatisfy` identity
      isValidHexColor theme.base05 `shouldSatisfy` identity

    it "generates theme for LCD monitor" do
      let theme = generateFleekTheme LCD
      isValidHexColor theme.base00 `shouldSatisfy` identity
      isValidHexColor theme.base05 `shouldSatisfy` identity

    it "generates all Base16 colors as valid hex" do
      let theme = generateFleekTheme OLED
      isValidHexColor theme.base00 `shouldSatisfy` identity
      isValidHexColor theme.base05 `shouldSatisfy` identity
      isValidHexColor theme.base0A `shouldSatisfy` identity
      isValidHexColor theme.base0F `shouldSatisfy` identity

-- | Property: All generated theme colors are valid hex format
prop_themeColorsValidHex :: Boolean -> Boolean
prop_themeColorsValidHex useOled =
  let monitorType = if useOled then OLED else LCD
      theme = generateHolographicTheme monitorType
  in isValidHexColor theme.base00
     && isValidHexColor theme.base05
     && isValidHexColor theme.base08
     && isValidHexColor theme.base0A
     && isValidHexColor theme.base0D
     && isValidHexColor theme.base0F

-- | Property: Theme generation is deterministic
prop_themeGenerationDeterministic :: Boolean -> Boolean
prop_themeGenerationDeterministic useOled =
  let monitorType = if useOled then OLED else LCD
      t1 = generateHolographicTheme monitorType
      t2 = generateHolographicTheme monitorType
      f1 = generateFleekTheme monitorType
      f2 = generateFleekTheme monitorType
  in t1.base00 == t2.base00
     && t1.base05 == t2.base05
     && t1.base0A == t2.base0A
     && f1.base00 == f2.base00
     && f1.base05 == f2.base05

-- | Property tests
testProperties :: Spec Unit
testProperties =
  describe "Property Tests" do
    it "theme colors are always valid hex colors" do
      liftEffect $ quickCheck prop_themeColorsValidHex

    it "theme generation is deterministic" do
      liftEffect $ quickCheck prop_themeGenerationDeterministic
