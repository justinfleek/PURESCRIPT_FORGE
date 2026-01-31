-- | Unit tests for currency formatting
module Test.Sidepanel.Utils.CurrencySpec where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Sidepanel.Utils.Currency (formatDiem, formatUSD, formatNumber, formatConsumptionRate, formatTimeToDepletion)

spec :: Spec Unit
spec = describe "Currency Formatting" do
  describe "formatDiem" do
    it "formats whole Diem amounts" do
      formatDiem 42.5 `shouldEqual` "42.50 Diem"
      formatDiem 100.0 `shouldEqual` "100 Diem"
      formatDiem 1.0 `shouldEqual` "1.00 Diem"
      formatDiem 1.5 `shouldEqual` "1.50 Diem"
    
    it "formats fractional Diem as cents" do
      formatDiem 0.5 `shouldEqual` "50.00¢"
      formatDiem 0.01 `shouldEqual` "1.00¢"
      formatDiem 0.99 `shouldEqual` "99.00¢"
      formatDiem 0.1 `shouldEqual` "10.00¢"
    
    it "formats zero correctly" do
      formatDiem 0.0 `shouldEqual` "0.00¢"
    
    it "formats very small values" do
      formatDiem 0.001 `shouldEqual` "0.10¢"
      formatDiem 0.0001 `shouldEqual` "0.01¢"
      formatDiem 0.00001 `shouldEqual` "0.00¢"
    
    it "formats very large values" do
      formatDiem 1000.0 `shouldEqual` "1000 Diem"
      formatDiem 1.0e6 `shouldEqual` "1000000 Diem"
      formatDiem 1000000.5 `shouldEqual` "1000000.50 Diem"
    
    it "formats boundary values" do
      formatDiem 0.99 `shouldEqual` "99.00¢"
      formatDiem 1.0 `shouldEqual` "1.00 Diem"
      formatDiem 1.01 `shouldEqual` "1.01 Diem"
      formatDiem 0.999 `shouldEqual` "99.90¢"
      formatDiem 0.9999 `shouldEqual` "99.99¢"
  
  describe "formatUSD" do
    it "formats USD with dollar sign" do
      formatUSD 10.5 `shouldEqual` "$10.50"
      formatUSD 0.5 `shouldEqual` "$0.50"
      formatUSD 100.5 `shouldEqual` "$100.50"
    
    it "formats whole dollar amounts" do
      formatUSD 100.0 `shouldEqual` "$100"
      formatUSD 0.0 `shouldEqual` "$0"
      formatUSD 1000.0 `shouldEqual` "$1000"
    
    it "formats zero correctly" do
      formatUSD 0.0 `shouldEqual` "$0"
    
    it "formats very small values" do
      formatUSD 0.01 `shouldEqual` "$0.01"
      formatUSD 0.001 `shouldEqual` "$0.00" -- Would verify rounding
    
    it "formats very large values" do
      formatUSD 1000000.0 `shouldEqual` "$1000000"
      formatUSD 1.0e6 `shouldEqual` "$1000000"
    
    it "formats fractional cents correctly" do
      formatUSD 10.999 `shouldEqual` "$11.00" -- Would verify rounding
      formatUSD 10.995 `shouldEqual` "$11.00" -- Would verify rounding
  
  describe "formatNumber" do
    it "formats numbers with 2 decimals" do
      formatNumber 42.567 `shouldEqual` "42.57"
      formatNumber 42.561 `shouldEqual` "42.56"
      formatNumber 42.565 `shouldEqual` "42.57"
      formatNumber 42.564 `shouldEqual` "42.56"
    
    it "removes .00 for whole numbers" do
      formatNumber 100.0 `shouldEqual` "100"
      formatNumber 0.0 `shouldEqual` "0"
      formatNumber 42.0 `shouldEqual` "42"
      formatNumber 1.0 `shouldEqual` "1"
      formatNumber 1000.0 `shouldEqual` "1000"
    
    it "formats zero correctly" do
      formatNumber 0.0 `shouldEqual` "0"
    
    it "formats very small numbers" do
      formatNumber 0.001 `shouldEqual` "0.00"
      formatNumber 0.01 `shouldEqual` "0.01"
      formatNumber 0.009 `shouldEqual` "0.01"
      formatNumber 0.004 `shouldEqual` "0.00"
    
    it "formats very large numbers" do
      formatNumber 1000000.0 `shouldEqual` "1000000"
      formatNumber 1.0e6 `shouldEqual` "1000000"
      formatNumber 1000000.5 `shouldEqual` "1000000.50"
    
    it "handles rounding correctly" do
      formatNumber 42.994 `shouldEqual` "42.99"
      formatNumber 42.995 `shouldEqual` "43.00"
      formatNumber 42.996 `shouldEqual` "43.00"
      formatNumber 42.9949 `shouldEqual` "42.99"
      formatNumber 42.9951 `shouldEqual` "43.00"
    
    it "handles edge cases around .00 boundary" do
      formatNumber 42.999 `shouldEqual` "43.00"
      formatNumber 42.001 `shouldEqual` "42.00"
      formatNumber 42.9999 `shouldEqual` "43.00"
      formatNumber 42.0001 `shouldEqual` "42.00"
  
  describe "formatConsumptionRate" do
    it "formats rate per hour" do
      formatConsumptionRate 2.5 `shouldEqual` "$2.50/hr"
      formatConsumptionRate 0.5 `shouldEqual` "$0.50/hr"
      formatConsumptionRate 100.0 `shouldEqual` "$100/hr"
    
    it "formats zero rate" do
      formatConsumptionRate 0.0 `shouldEqual` "$0/hr"
    
    it "formats very small rates" do
      formatConsumptionRate 0.01 `shouldEqual` "$0.01/hr"
      formatConsumptionRate 0.001 `shouldEqual` "$0.00/hr" -- Would verify rounding
    
    it "formats very large rates" do
      formatConsumptionRate 1000.0 `shouldEqual` "$1000/hr"
      formatConsumptionRate 1.0e6 `shouldEqual` "$1000000/hr"
  
  describe "formatTimeToDepletion" do
    it "formats minutes when under 1 hour" do
      formatTimeToDepletion 0.5 `shouldEqual` "30 minutes"
      formatTimeToDepletion 0.25 `shouldEqual` "15 minutes"
      formatTimeToDepletion 0.0167 `shouldEqual` "1 minutes" -- floor(0.0167 * 60) = 1
      formatTimeToDepletion 0.0333 `shouldEqual` "1 minutes" -- floor(0.0333 * 60) = 1
      formatTimeToDepletion 0.0166 `shouldEqual` "0 minutes" -- floor(0.0166 * 60) = 0
    
    it "formats exactly 1 hour" do
      formatTimeToDepletion 1.0 `shouldEqual` "1.00 hours"
    
    it "formats hours" do
      formatTimeToDepletion 5.5 `shouldEqual` "5.50 hours"
      formatTimeToDepletion 12.0 `shouldEqual` "12.00 hours"
      formatTimeToDepletion 23.5 `shouldEqual` "23.50 hours"
      formatTimeToDepletion 23.99 `shouldEqual` "23.99 hours"
    
    it "formats exactly 24 hours as 1 day" do
      formatTimeToDepletion 24.0 `shouldEqual` "1.00 days"
    
    it "formats days" do
      formatTimeToDepletion 48.0 `shouldEqual` "2.00 days"
      formatTimeToDepletion 72.0 `shouldEqual` "3.00 days"
      formatTimeToDepletion 168.0 `shouldEqual` "7.00 days"
      formatTimeToDepletion 240.0 `shouldEqual` "10.00 days"
    
    it "formats zero correctly" do
      formatTimeToDepletion 0.0 `shouldEqual` "0 minutes"
    
    it "formats very small values" do
      formatTimeToDepletion 0.0001 `shouldEqual` "0 minutes" -- floor(0.0001 * 60) = 0
      formatTimeToDepletion 0.001 `shouldEqual` "0 minutes" -- floor(0.001 * 60) = 0
      formatTimeToDepletion 0.01 `shouldEqual` "0 minutes" -- floor(0.01 * 60) = 0
    
    it "formats very large values" do
      formatTimeToDepletion 720.0 `shouldEqual` "30.00 days"
      formatTimeToDepletion 8760.0 `shouldEqual` "365.00 days"
      formatTimeToDepletion 17520.0 `shouldEqual` "730.00 days"
    
    it "handles boundary values" do
      formatTimeToDepletion 0.999 `shouldEqual` "59 minutes" -- floor(0.999 * 60) = 59
      formatTimeToDepletion 1.0 `shouldEqual` "1.00 hours"
      formatTimeToDepletion 1.001 `shouldEqual` "1.00 hours"
      formatTimeToDepletion 23.999 `shouldEqual` "23.99 hours"
      formatTimeToDepletion 24.0 `shouldEqual` "1.00 days"
      formatTimeToDepletion 24.001 `shouldEqual` "1.00 days"
    
    it "handles fractional days correctly" do
      formatTimeToDepletion 36.0 `shouldEqual` "1.50 days"
      formatTimeToDepletion 48.5 `shouldEqual` "2.02 days" -- Would verify calculation
      formatTimeToDepletion 72.5 `shouldEqual` "3.02 days" -- Would verify calculation