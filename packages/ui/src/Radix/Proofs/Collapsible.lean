/-
  Collapsible Component Proofs
  
  Lean4 verified specification for Collapsible component.
  No sorry, no axioms, no escapes.
  
  Invariants:
  - CollapsibleVariant is exactly one of two values (Normal, Ghost)
  - State is exactly one of two values (Open, Closed)
  - Disabled collapsibles cannot be toggled
  - State transitions are deterministic
-/

namespace Radix.Proofs.Collapsible

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES (Finite, Exhaustive)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Collapsible variant is exactly one of two values -/
inductive CollapsibleVariant where
  | normal
  | ghost
  deriving Repr, BEq, DecidableEq

/-- Collapsible state is exactly one of two values -/
inductive CollapsibleOpenState where
  | open
  | closed
  deriving Repr, BEq, DecidableEq

/-- Collapsible component state -/
structure CollapsibleState where
  isOpen : Bool
  disabled : Bool
  variant : CollapsibleVariant

/-- Collapsible output events -/
inductive CollapsibleOutput where
  | openChanged (isOpen : Bool)

-- ═══════════════════════════════════════════════════════════════════════════════
-- THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Variant string conversion is total -/
def variantToString : CollapsibleVariant → String
  | .normal => "normal"
  | .ghost => "ghost"

/-- Variant string conversion never produces empty string -/
theorem variantToString_nonEmpty (v : CollapsibleVariant) : (variantToString v).length > 0 := by
  cases v <;> decide

/-- State to data-state attribute -/
def stateToDataAttr (isOpen : Bool) : String :=
  if isOpen then "open" else "closed"

/-- State string is always non-empty -/
theorem stateToDataAttr_nonEmpty (isOpen : Bool) : (stateToDataAttr isOpen).length > 0 := by
  simp [stateToDataAttr]
  split <;> decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- STATE TRANSITIONS (Total Functions)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- All possible collapsible actions -/
inductive CollapsibleAction where
  | handleTriggerClick
  | receive (newState : CollapsibleState)

/-- Toggle the open state -/
def toggle (isOpen : Bool) : Bool := !isOpen

/-- State transition function (total, deterministic) -/
def handleAction (state : CollapsibleState) (action : CollapsibleAction) 
    : CollapsibleState × Option CollapsibleOutput :=
  match action with
  | .handleTriggerClick =>
    if state.disabled then
      (state, none)  -- No change when disabled
    else
      let newOpen := toggle state.isOpen
      ({ state with isOpen := newOpen }, some (.openChanged newOpen))
  | .receive newState =>
    (newState, none)

/-- Theorem: handleAction is total -/
theorem handleAction_total (state : CollapsibleState) (action : CollapsibleAction) :
    ∃ (newState : CollapsibleState) (output : Option CollapsibleOutput),
      handleAction state action = (newState, output) := by
  exists (handleAction state action).1
  exists (handleAction state action).2
  simp

/-- Theorem: disabled collapsible never changes state on click -/
theorem disabled_no_change (state : CollapsibleState) (h : state.disabled = true) :
    (handleAction state .handleTriggerClick).1 = state := by
  simp [handleAction, h]

/-- Theorem: enabled collapsible toggles on click -/
theorem enabled_toggles (state : CollapsibleState) (h : state.disabled = false) :
    (handleAction state .handleTriggerClick).1.isOpen = !state.isOpen := by
  simp [handleAction, h, toggle]

/-- Theorem: click on enabled always emits output -/
theorem enabled_emits_output (state : CollapsibleState) (h : state.disabled = false) :
    (handleAction state .handleTriggerClick).2.isSome = true := by
  simp [handleAction, h]

/-- Theorem: click on disabled never emits output -/
theorem disabled_no_output (state : CollapsibleState) (h : state.disabled = true) :
    (handleAction state .handleTriggerClick).2 = none := by
  simp [handleAction, h]

-- ═══════════════════════════════════════════════════════════════════════════════
-- TOGGLE PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Toggle is self-inverse -/
theorem toggle_involutive (b : Bool) : toggle (toggle b) = b := by
  simp [toggle]

/-- Toggle changes the value -/
theorem toggle_changes (b : Bool) : toggle b ≠ b := by
  simp [toggle]

/-- Double click returns to original state (when enabled) -/
theorem double_click_identity (state : CollapsibleState) (h : state.disabled = false) :
    let s1 := (handleAction state .handleTriggerClick).1
    let s2 := (handleAction s1 .handleTriggerClick).1
    s2.isOpen = state.isOpen := by
  simp [handleAction, h, toggle]
  -- After first click: isOpen = !state.isOpen
  -- s1.disabled = state.disabled = false
  -- After second click: isOpen = !(!state.isOpen) = state.isOpen
  split
  · -- state.isOpen = true case
    simp
  · -- state.isOpen = false case
    simp

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACCESSIBILITY INVARIANTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- ARIA expanded attribute matches state -/
def ariaExpanded (state : CollapsibleState) : String :=
  if state.isOpen then "true" else "false"

/-- Theorem: ariaExpanded is consistent with state -/
theorem ariaExpanded_consistent (state : CollapsibleState) :
    (ariaExpanded state = "true") ↔ state.isOpen = true := by
  simp [ariaExpanded]
  constructor
  · intro h
    split at h <;> simp_all
  · intro h
    simp [h]

end Radix.Proofs.Collapsible
