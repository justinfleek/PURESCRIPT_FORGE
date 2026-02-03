/-
  Button Component Proofs
  
  Lean4 verified specification for Button component.
  No sorry, no axioms, no escapes.
  
  Invariants:
  - Button size is one of exactly three values
  - Button variant is one of exactly three values
  - Click events only fire when button is not disabled
  - Label is non-empty when rendered
-/

namespace Radix.Proofs.Button

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES (Finite, Exhaustive)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Button size is exactly one of three values -/
inductive ButtonSize where
  | small
  | normal
  | large
  deriving Repr, BEq, DecidableEq

/-- Button variant is exactly one of three values -/
inductive ButtonVariant where
  | primary
  | secondary
  | ghost
  deriving Repr, BEq, DecidableEq

/-- Non-empty string type with proof -/
structure NonEmptyString where
  value : String
  nonEmpty : value.length > 0

/-- Button state (deterministic, total) -/
structure ButtonState where
  size : ButtonSize
  variant : ButtonVariant
  disabled : Bool
  label : NonEmptyString
  hasIcon : Bool

/-- Button output events (exhaustive) -/
inductive ButtonOutput where
  | clicked

-- ═══════════════════════════════════════════════════════════════════════════════
-- THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Button size string conversion is total -/
def sizeToString : ButtonSize → String
  | .small => "small"
  | .normal => "normal"
  | .large => "large"

/-- Button variant string conversion is total -/
def variantToString : ButtonVariant → String
  | .primary => "primary"
  | .secondary => "secondary"
  | .ghost => "ghost"

/-- Size string conversion never produces empty string -/
theorem sizeToString_nonEmpty (s : ButtonSize) : (sizeToString s).length > 0 := by
  cases s <;> decide

/-- Variant string conversion never produces empty string -/  
theorem variantToString_nonEmpty (v : ButtonVariant) : (variantToString v).length > 0 := by
  cases v <;> decide

/-- Click event only fires when not disabled -/
structure ClickEvent where
  state : ButtonState
  notDisabled : state.disabled = false

/-- Theorem: click event implies button was enabled -/
theorem clickRequiresEnabled (event : ClickEvent) : event.state.disabled = false :=
  event.notDisabled

/-- Button label is always non-empty -/
theorem labelNonEmpty (state : ButtonState) : state.label.value.length > 0 :=
  state.label.nonEmpty

-- ═══════════════════════════════════════════════════════════════════════════════
-- STATE TRANSITIONS (Total Functions)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- All possible button actions -/
inductive ButtonAction where
  | handleClick
  | receive (newState : ButtonState)

/-- State transition function (total, deterministic) -/
def handleAction (state : ButtonState) (action : ButtonAction) : ButtonState × Option ButtonOutput :=
  match action with
  | .handleClick =>
    if state.disabled then
      (state, none)  -- No output when disabled
    else
      (state, some .clicked)  -- Output click when enabled
  | .receive newState =>
    (newState, none)

/-- Theorem: handleAction is total (always produces valid result) -/
theorem handleAction_total (state : ButtonState) (action : ButtonAction) :
  ∃ (newState : ButtonState) (output : Option ButtonOutput),
    handleAction state action = (newState, output) := by
  exists (handleAction state action).1
  exists (handleAction state action).2
  simp

/-- Theorem: disabled button never emits click -/
theorem disabled_no_click (state : ButtonState) (h : state.disabled = true) :
  (handleAction state .handleClick).2 = none := by
  simp [handleAction, h]

/-- Theorem: enabled button always emits click on handleClick -/
theorem enabled_emits_click (state : ButtonState) (h : state.disabled = false) :
  (handleAction state .handleClick).2 = some .clicked := by
  simp [handleAction, h]

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER INVARIANTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Data attributes for button rendering -/
structure ButtonDataAttrs where
  component : String
  size : String
  variant : String
  sizeNonEmpty : size.length > 0
  variantNonEmpty : variant.length > 0

/-- Create data attributes from state (total, produces valid attrs) -/
def mkDataAttrs (state : ButtonState) : ButtonDataAttrs :=
  { component := "button"
  , size := sizeToString state.size
  , variant := variantToString state.variant
  , sizeNonEmpty := sizeToString_nonEmpty state.size
  , variantNonEmpty := variantToString_nonEmpty state.variant
  }

/-- Theorem: data attrs from any state are valid -/
theorem mkDataAttrs_valid (state : ButtonState) :
  (mkDataAttrs state).size.length > 0 ∧ (mkDataAttrs state).variant.length > 0 := by
  constructor
  · exact sizeToString_nonEmpty state.size
  · exact variantToString_nonEmpty state.variant

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACCESSIBILITY INVARIANTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Button always has accessible name via label -/
theorem buttonHasAccessibleName (state : ButtonState) :
  state.label.value.length > 0 :=
  state.label.nonEmpty

/-- Disabled attribute matches state -/
def ariaDisabled (state : ButtonState) : String :=
  if state.disabled then "true" else "false"

/-- Theorem: ariaDisabled is consistent with state -/
theorem ariaDisabled_consistent (state : ButtonState) :
  (ariaDisabled state = "true") ↔ state.disabled = true := by
  simp [ariaDisabled]
  constructor
  · intro h
    split at h <;> simp_all
  · intro h
    simp [h]

end Radix.Proofs.Button
