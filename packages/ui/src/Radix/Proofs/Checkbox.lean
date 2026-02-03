/-
  Checkbox Component Proofs
  
  Lean4 verified specification for Checkbox component.
  No sorry, no axioms, no escapes.
  
  Invariants:
  - Checkbox state is exactly one of three values (Checked, Unchecked, Indeterminate)
  - Disabled checkboxes cannot be toggled
  - State transitions are deterministic
  - Toggle from Indeterminate goes to Checked
-/

namespace Radix.Proofs.Checkbox

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES (Finite, Exhaustive)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Checkbox state is exactly one of three values -/
inductive CheckState where
  | checked
  | unchecked
  | indeterminate
  deriving Repr, BEq, DecidableEq

/-- Checkbox component state -/
structure CheckboxState where
  checkState : CheckState
  disabled : Bool

/-- Checkbox output events -/
inductive CheckboxOutput where
  | checkedChanged (state : CheckState)

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONVERSION FUNCTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- State to string (for data-state attribute) -/
def stateToString : CheckState → String
  | .checked => "checked"
  | .unchecked => "unchecked"
  | .indeterminate => "indeterminate"

/-- State to boolean (for form submission) -/
def stateToBoolean : CheckState → Bool
  | .checked => true
  | .unchecked => false
  | .indeterminate => false  -- Treat as unchecked

/-- ARIA checked attribute (supports mixed) -/
def ariaChecked : CheckState → String
  | .checked => "true"
  | .unchecked => "false"
  | .indeterminate => "mixed"

-- ═══════════════════════════════════════════════════════════════════════════════
-- THEOREMS (String conversions)
-- ═══════════════════════════════════════════════════════════════════════════════

theorem stateToString_nonEmpty (s : CheckState) : (stateToString s).length > 0 := by
  cases s <;> decide

theorem ariaChecked_nonEmpty (s : CheckState) : (ariaChecked s).length > 0 := by
  cases s <;> decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- STATE TRANSITIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Checkbox actions -/
inductive CheckboxAction where
  | handleClick
  | setChecked (state : CheckState)
  | receive (newState : CheckboxState)

/-- Toggle state: Checked -> Unchecked, Unchecked -> Checked, Indeterminate -> Checked -/
def toggleState : CheckState → CheckState
  | .checked => .unchecked
  | .unchecked => .checked
  | .indeterminate => .checked

/-- State transition function (total, deterministic) -/
def handleAction (state : CheckboxState) (action : CheckboxAction) 
    : CheckboxState × Option CheckboxOutput :=
  match action with
  | .handleClick =>
    if state.disabled then
      (state, none)
    else
      let newState := toggleState state.checkState
      ({ state with checkState := newState }, some (.checkedChanged newState))
  | .setChecked checkState =>
    if checkState == state.checkState then
      (state, none)
    else
      ({ state with checkState := checkState }, some (.checkedChanged checkState))
  | .receive newState =>
    (newState, none)

-- ═══════════════════════════════════════════════════════════════════════════════
-- THEOREMS (State transitions)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Theorem: handleAction is total -/
theorem handleAction_total (state : CheckboxState) (action : CheckboxAction) :
    ∃ (newState : CheckboxState) (output : Option CheckboxOutput),
      handleAction state action = (newState, output) := by
  exists (handleAction state action).1
  exists (handleAction state action).2
  simp

/-- Theorem: disabled checkbox never changes state on click -/
theorem disabled_no_change (state : CheckboxState) (h : state.disabled = true) :
    (handleAction state .handleClick).1 = state := by
  simp [handleAction, h]

/-- Theorem: enabled checkbox toggles on click -/
theorem enabled_toggles (state : CheckboxState) (h : state.disabled = false) :
    (handleAction state .handleClick).1.checkState = toggleState state.checkState := by
  simp [handleAction, h]

/-- Theorem: click on enabled always emits output -/
theorem enabled_emits_output (state : CheckboxState) (h : state.disabled = false) :
    (handleAction state .handleClick).2.isSome = true := by
  simp [handleAction, h]

/-- Theorem: click on disabled never emits output -/
theorem disabled_no_output (state : CheckboxState) (h : state.disabled = true) :
    (handleAction state .handleClick).2 = none := by
  simp [handleAction, h]

/-- Theorem: toggle from checked/unchecked is binary cycle -/
theorem toggle_binary_cycle (s : CheckState) (h : s ≠ .indeterminate) :
    toggleState (toggleState s) = s := by
  cases s with
  | checked => rfl
  | unchecked => rfl
  | indeterminate => contradiction

/-- Theorem: indeterminate -> checked on click -/
theorem indeterminate_becomes_checked :
    toggleState .indeterminate = .checked := by
  rfl

/-- Theorem: checked -> unchecked on click -/
theorem checked_becomes_unchecked :
    toggleState .checked = .unchecked := by
  rfl

/-- Theorem: unchecked -> checked on click -/
theorem unchecked_becomes_checked :
    toggleState .unchecked = .checked := by
  rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- FORM SUBMISSION INVARIANTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Theorem: only checked state submits as true -/
theorem only_checked_is_true (s : CheckState) :
    stateToBoolean s = true ↔ s = .checked := by
  cases s <;> simp [stateToBoolean]

/-- Theorem: indeterminate submits as false -/
theorem indeterminate_is_false :
    stateToBoolean .indeterminate = false := by
  rfl

end Radix.Proofs.Checkbox
