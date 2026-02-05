-- | Price Utility Module
-- |
-- | Provides price conversion utilities.
-- | Handles conversions between dollars, cents, and micro-cents.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/util/price.ts
module Forge.Console.Core.Util.Price
  ( Dollars
  , Cents
  , MicroCents
  , dollarsToMicroCents
  , centsToMicroCents
  , microCentsToDollars
  , microCentsToCents
  , calculateFeeInCents
  ) where

import Prelude

import Data.Int (round, toNumber)

-- | Type aliases for currency units
type Dollars = Number
type Cents = Int
type MicroCents = Int

-- | Micro-cents per cent (10000 micro-cents = 1 cent)
microCentsPerCent :: Int
microCentsPerCent = 10000

-- | Micro-cents per dollar (1000000 micro-cents = 1 dollar)
microCentsPerDollar :: Int
microCentsPerDollar = 1000000

-- | Convert dollars to micro-cents
dollarsToMicroCents :: Dollars -> MicroCents
dollarsToMicroCents dollars = round (dollars * toNumber microCentsPerDollar)

-- | Convert cents to micro-cents
centsToMicroCents :: Cents -> MicroCents
centsToMicroCents cents = cents * microCentsPerCent

-- | Convert micro-cents to dollars
microCentsToDollars :: MicroCents -> Dollars
microCentsToDollars microCents = toNumber microCents / toNumber microCentsPerDollar

-- | Convert micro-cents to cents
microCentsToCents :: MicroCents -> Cents
microCentsToCents microCents = microCents / microCentsPerCent

-- | Calculate processing fee in cents
-- | Uses formula: fee = ((amount + 30) / 0.956) * 0.044 + 30
-- | This accounts for ~4.4% Stripe fee + $0.30 fixed fee
calculateFeeInCents :: Cents -> Cents
calculateFeeInCents amount = 
  let amountNum = toNumber amount
      fee = ((amountNum + 30.0) / 0.956) * 0.044 + 30.0
  in round fee
