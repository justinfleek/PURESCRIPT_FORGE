-- | Diff Changes Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/diff-changes.tsx (116 lines)
-- |
-- | Displays addition/deletion counts as text or colored bars.
-- | Two variants: "default" (text) and "bars" (visual).
-- | Pure Halogen implementation.
-- |
-- | Data Attributes:
-- | - `data-component="diff-changes"` - Root element
-- | - `data-variant="default|bars"` - Display variant
-- | - `data-slot="diff-changes-additions"` - Additions count
-- | - `data-slot="diff-changes-deletions"` - Deletions count
module UI.Components.DiffChanges
  ( component
  , Input
  , DiffChange
  , DiffChangesVariant(..)
  , defaultInput
  ) where

import Prelude

import Data.Array (foldl, replicate, take)
import Data.Int (toNumber, round)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Single diff change
type DiffChange =
  { additions :: Int
  , deletions :: Int
  }

-- | Display variant
data DiffChangesVariant
  = Default   -- Text: "+5 -3"
  | Bars      -- Visual bars

derive instance eqDiffChangesVariant :: Eq DiffChangesVariant

variantToString :: DiffChangesVariant -> String
variantToString Default = "default"
variantToString Bars = "bars"

-- | Input props
type Input =
  { changes :: Array DiffChange    -- Array of changes to sum
  , variant :: DiffChangesVariant
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { changes: []
  , variant: Default
  , className: Nothing
  }

-- | Internal state (stateless component)
type State = { input :: Input }

-- | Internal actions
data Action = Receive Input

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

component :: forall q o m. MonadAff m => H.Component q Input o m
component = H.mkComponent
  { initialState: \input -> { input }
  , render
  , eval: H.mkEval $ H.defaultEval
      { receive = Just <<< Receive
      }
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  let
    totals = calculateTotals state.input.changes
  in
    HH.div
      ([ HP.attr (HH.AttrName "data-component") "diff-changes"
      , HP.attr (HH.AttrName "data-variant") (variantToString state.input.variant)
      ] <> classAttr state.input.className)
      [ case state.input.variant of
          Default -> renderDefault totals
          Bars -> renderBars totals
      ]

renderDefault :: forall m. { additions :: Int, deletions :: Int } -> H.ComponentHTML Action () m
renderDefault totals =
  if totals.additions == 0 && totals.deletions == 0
    then HH.text ""
    else HH.span_
      [ HH.span
          [ HP.attr (HH.AttrName "data-slot") "diff-changes-additions"
          , HP.class_ (HH.ClassName "additions")
          ]
          [ HH.text ("+" <> show totals.additions) ]
      , HH.text " "
      , HH.span
          [ HP.attr (HH.AttrName "data-slot") "diff-changes-deletions"
          , HP.class_ (HH.ClassName "deletions")
          ]
          [ HH.text ("-" <> show totals.deletions) ]
      ]

renderBars :: forall m. { additions :: Int, deletions :: Int } -> H.ComponentHTML Action () m
renderBars totals =
  let
    blockCounts = calculateBlockCounts totals.additions totals.deletions
    blocks = visibleBlocks blockCounts
  in
    HH.element (HH.ElemName "svg")
      [ HP.attr (HH.AttrName "viewBox") "0 0 18 12"
      , HP.attr (HH.AttrName "aria-hidden") "true"
      ]
      (mapWithIndex renderBlock blocks)

renderBlock :: forall m. Int -> String -> H.ComponentHTML Action () m
renderBlock index color =
  HH.element (HH.ElemName "rect")
    [ HP.attr (HH.AttrName "x") (show (index * 4))
    , HP.attr (HH.AttrName "y") "0"
    , HP.attr (HH.AttrName "width") "2"
    , HP.attr (HH.AttrName "height") "12"
    , HP.attr (HH.AttrName "rx") "1"
    , HP.attr (HH.AttrName "fill") color
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
-- CALCULATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calculate total additions and deletions
calculateTotals :: Array DiffChange -> { additions :: Int, deletions :: Int }
calculateTotals changes =
  foldl 
    (\acc c -> { additions: acc.additions + c.additions, deletions: acc.deletions + c.deletions })
    { additions: 0, deletions: 0 }
    changes

-- | CSS color variables
addColor :: String
addColor = "var(--icon-diff-add-base)"

deleteColor :: String
deleteColor = "var(--icon-diff-delete-base)"

neutralColor :: String
neutralColor = "var(--icon-weak-base)"

-- | Total number of blocks for bar display
totalBlocks :: Int
totalBlocks = 5

-- | Block counts for bar display
type BlockCounts =
  { added :: Int
  , deleted :: Int
  , neutral :: Int
  }

-- | Calculate block counts based on additions/deletions
calculateBlockCounts :: Int -> Int -> BlockCounts
calculateBlockCounts adds dels
  | adds == 0 && dels == 0 = 
      { added: 0, deleted: 0, neutral: totalBlocks }
  | otherwise =
      let
        total = adds + dels
        
        -- For small totals, just show presence
        smallResult = 
          let added = if adds > 0 then 1 else 0
              deleted = if dels > 0 then 1 else 0
          in { added, deleted, neutral: totalBlocks - added - deleted }
        
        -- For larger totals, calculate proportionally
        largeResult =
          let
            ratio = if adds > dels 
              then toNumber adds / toNumber (max 1 dels)
              else toNumber dels / toNumber (max 1 adds)
            
            colorBlocks = if total < 20 || ratio < 4.0 
              then totalBlocks - 1 
              else totalBlocks
            
            percentAdded = toNumber adds / toNumber total
            percentDeleted = toNumber dels / toNumber total
            
            addedRaw = percentAdded * toNumber colorBlocks
            deletedRaw = percentDeleted * toNumber colorBlocks
            
            added' = if adds > 0 then max 1 (round addedRaw) else 0
            deleted' = if dels > 0 then max 1 (round deletedRaw) else 0
            
            -- Cap based on magnitude
            added = capBlocks adds added'
            deleted = capBlocks dels deleted'
            
            -- Ensure total doesn't exceed colorBlocks
            totalAllocated = added + deleted
            finalAdded = if totalAllocated > colorBlocks
              then if addedRaw > deletedRaw then colorBlocks - deleted else added
              else added
            finalDeleted = if totalAllocated > colorBlocks
              then if addedRaw <= deletedRaw then colorBlocks - added else deleted
              else deleted
            
            neutral = max 0 (totalBlocks - finalAdded - finalDeleted)
          in { added: finalAdded, deleted: finalDeleted, neutral }
      in
        if total < 5 then smallResult else largeResult

-- | Cap blocks based on change magnitude
capBlocks :: Int -> Int -> Int
capBlocks count blocks
  | count > 0 && count <= 5 = min blocks 1
  | count > 5 && count <= 10 = min blocks 2
  | otherwise = blocks

-- | Generate visible blocks with colors
visibleBlocks :: BlockCounts -> Array String
visibleBlocks counts =
  let
    addBlocks = replicate counts.added addColor
    delBlocks = replicate counts.deleted deleteColor
    neutBlocks = replicate counts.neutral neutralColor
  in
    take totalBlocks (addBlocks <> delBlocks <> neutBlocks)

-- ═══════════════════════════════════════════════════════════════════════════════
-- HELPERS
-- ═══════════════════════════════════════════════════════════════════════════════

mapWithIndex :: forall a b. (Int -> a -> b) -> Array a -> Array b
mapWithIndex f arr = mapWithIndexImpl f arr 0

mapWithIndexImpl :: forall a b. (Int -> a -> b) -> Array a -> Int -> Array b
mapWithIndexImpl f arr idx = case uncons arr of
  Nothing -> []
  Just { head, tail } -> 
    [f idx head] <> mapWithIndexImpl f tail (idx + 1)

foreign import uncons :: forall a. Array a -> Maybe { head :: a, tail :: Array a }

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO EXTERNAL FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only standard Halogen/Web APIs.
-- All calculations are pure PureScript.
