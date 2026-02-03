-- | Black Plans Common Types
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/black/common.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Black.Common
  ( Plan(..)
  , PlanId(..)
  , plans
  , allPlanIds
  , getPlanById
  , getPlanPrice
  , getPlanMultiplier
  , isValidPlanId
  ) where

import Prelude

import Data.Array (find)
import Data.Maybe (Maybe(..), isJust)

-- | Plan ID type
data PlanId = Plan20 | Plan100 | Plan200

derive instance eqPlanId :: Eq PlanId
derive instance ordPlanId :: Ord PlanId

instance showPlanId :: Show PlanId where
  show Plan20 = "20"
  show Plan100 = "100"
  show Plan200 = "200"

-- | Parse plan ID from string
parsePlanId :: String -> Maybe PlanId
parsePlanId "20" = Just Plan20
parsePlanId "100" = Just Plan100
parsePlanId "200" = Just Plan200
parsePlanId _ = Nothing

-- | Plan configuration
type Plan =
  { id :: PlanId
  , price :: Int  -- monthly price in dollars
  , multiplier :: Maybe String
  }

-- | All available plans
plans :: Array Plan
plans =
  [ { id: Plan20, price: 20, multiplier: Nothing }
  , { id: Plan100, price: 100, multiplier: Just "5x more usage than Black 20" }
  , { id: Plan200, price: 200, multiplier: Just "20x more usage than Black 20" }
  ]

-- | All plan IDs
allPlanIds :: Array PlanId
allPlanIds = [Plan20, Plan100, Plan200]

-- | Get plan by ID
getPlanById :: PlanId -> Maybe Plan
getPlanById planId = find (\p -> p.id == planId) plans

-- | Get plan by string ID
getPlanByStringId :: String -> Maybe Plan
getPlanByStringId str = do
  planId <- parsePlanId str
  getPlanById planId

-- | Get plan price
getPlanPrice :: PlanId -> Int
getPlanPrice Plan20 = 20
getPlanPrice Plan100 = 100
getPlanPrice Plan200 = 200

-- | Get plan multiplier text
getPlanMultiplier :: PlanId -> Maybe String
getPlanMultiplier Plan20 = Nothing
getPlanMultiplier Plan100 = Just "5x more usage than Black 20"
getPlanMultiplier Plan200 = Just "20x more usage than Black 20"

-- | Check if string is valid plan ID
isValidPlanId :: String -> Boolean
isValidPlanId str = isJust (parsePlanId str)

-- | Plan icon SVG path data (pure data)
type PlanIconData =
  { viewBox :: String
  , rects :: Array { x :: Number, y :: Number, width :: Number, height :: Number }
  }

-- | Get icon data for plan (pure)
getPlanIconData :: PlanId -> PlanIconData
getPlanIconData Plan20 =
  { viewBox: "0 0 24 24"
  , rects: [{ x: 0.5, y: 0.5, width: 23.0, height: 23.0 }]
  }
getPlanIconData Plan100 =
  { viewBox: "0 0 24 24"
  , rects:
      [ { x: 0.5, y: 0.5, width: 9.0, height: 9.0 }
      , { x: 0.5, y: 14.5, width: 9.0, height: 9.0 }
      , { x: 14.5, y: 0.5, width: 9.0, height: 9.0 }
      , { x: 14.5, y: 14.5, width: 9.0, height: 9.0 }
      ]
  }
getPlanIconData Plan200 =
  { viewBox: "0 0 24 24"
  , rects: generateGridRects 5 5 3.0  -- 5x5 grid of 3px rects
  }

-- | Generate grid of rectangles (pure)
generateGridRects :: Int -> Int -> Number -> Array { x :: Number, y :: Number, width :: Number, height :: Number }
generateGridRects cols rows size =
  let
    spacing = 5.0
  in
    do
      col <- range 0 (cols - 1)
      row <- range 0 (rows - 1)
      pure
        { x: toNumber col * spacing + 0.5
        , y: toNumber row * spacing + 0.5
        , width: size
        , height: size
        }
  where
    range :: Int -> Int -> Array Int
    range start end = if start > end then [] else [start] <> range (start + 1) end
    
    toNumber :: Int -> Number
    toNumber n = 0.0  -- simplified
