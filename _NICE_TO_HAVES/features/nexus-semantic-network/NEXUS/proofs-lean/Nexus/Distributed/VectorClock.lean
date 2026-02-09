-- | Nexus Distributed Semantic Memory - Vector Clock Causal Ordering Proofs
-- | Formal proofs for vector clock causal ordering and happened-before relationships

import Std.Data.AssocList
import Mathlib.Data.Nat.Basic

-- | Vector clock: maps region IDs to logical timestamps
abbrev VectorClock := Std.AssocList String Nat

-- | Get timestamp for a region (defaults to 0)
def VectorClock.get (vc : VectorClock) (region : String) : Nat :=
  vc.lookup region |>.getD 0

-- | Vector clock comparison result
inductive VectorClockOrder where
  | LT  -- vc1 happened before vc2
  | EQ  -- vc1 equals vc2
  | GT  -- vc1 happened after vc2
  | CONCURRENT  -- vc1 and vc2 are concurrent

-- | Compare two vector clocks
-- | Returns LT if vc1 < vc2 (vc1 happened before vc2)
-- | Returns GT if vc1 > vc2 (vc1 happened after vc2)
-- | Returns EQ if vc1 == vc2
-- | Returns CONCURRENT if vc1 || vc2 (concurrent events)
def compareVectorClocks (vc1 vc2 : VectorClock) : VectorClockOrder :=
  let allRegions := (vc1.keys ++ vc2.keys).toFinset
  let vc1Less := allRegions.toList.all (fun r => VectorClock.get vc1 r ≤ VectorClock.get vc2 r)
  let vc2Less := allRegions.toList.all (fun r => VectorClock.get vc2 r ≤ VectorClock.get vc1 r)
  let vc1StrictLess := allRegions.toList.any (fun r => VectorClock.get vc1 r < VectorClock.get vc2 r)
  let vc2StrictLess := allRegions.toList.any (fun r => VectorClock.get vc2 r < VectorClock.get vc1 r)
  if vc1Less && vc2Less then VectorClockOrder.EQ
  else if vc1Less && vc1StrictLess then VectorClockOrder.LT
  else if vc2Less && vc2StrictLess then VectorClockOrder.GT
  else VectorClockOrder.CONCURRENT

-- | Check if vc1 happened before vc2
def happenedBefore (vc1 vc2 : VectorClock) : Prop :=
  compareVectorClocks vc1 vc2 = VectorClockOrder.LT

-- | Helper lemma: If compareVectorClocks returns LT, then vc1 ≤ vc2 for all regions
lemma compareVectorClocks_LT_implies_le (vc1 vc2 : VectorClock) :
  compareVectorClocks vc1 vc2 = VectorClockOrder.LT →
  ∀ r : String, VectorClock.get vc1 r ≤ VectorClock.get vc2 r := by
  intro h_eq r
  unfold compareVectorClocks at h_eq
  -- The function returns LT only if vc1Less = true
  -- vc1Less checks allRegions.toList.all (fun r => vc1 r ≤ vc2 r)
  --
  -- Key insight: VectorClock.get defaults to 0 for missing regions
  -- Case 1: r ∈ allRegions (union of keys from vc1 and vc2)
  --   Then vc1Less = true implies VectorClock.get vc1 r ≤ VectorClock.get vc2 r
  -- Case 2: r ∉ allRegions
  --   Then r is not a key in either vc1 or vc2
  --   Therefore VectorClock.get vc1 r = 0 and VectorClock.get vc2 r = 0
  --   So 0 ≤ 0 holds trivially
  --
  -- Proof structure: Consider whether r is in allRegions or not
  by_cases h_mem : r ∈ (vc1.keys ++ vc2.keys).toFinset.toList
  · -- Case: r ∈ allRegions - the vc1Less check verified this
    -- When compareVectorClocks returns LT, vc1Less must be true
    -- vc1Less = allRegions.toList.all (fun r => VectorClock.get vc1 r ≤ VectorClock.get vc2 r)
    -- Since r ∈ allRegions.toList and vc1Less = true, we have VectorClock.get vc1 r ≤ VectorClock.get vc2 r
    -- Extract from the all-quantified check
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h_eq
    -- The check passed for all regions in allRegions, including r
    have h_all : (vc1.keys ++ vc2.keys).toFinset.toList.all
                   (fun r => VectorClock.get vc1 r ≤ VectorClock.get vc2 r) = true := by
      -- This follows from h_eq: LT is only returned when vc1Less = true
      split at h_eq <;> simp_all
    exact List.all_eq_true.mp h_all r h_mem
  · -- Case: r ∉ allRegions - both default to 0
    -- r is not in vc1.keys or vc2.keys, so lookup returns none, getD returns 0
    unfold VectorClock.get
    have h_not_in_vc1 : vc1.lookup r = none := by
      -- r ∉ (vc1.keys ++ vc2.keys).toFinset.toList
      -- Therefore r ∉ vc1.keys
      simp only [List.mem_toFinset, List.mem_append, not_or] at h_mem
      exact Std.AssocList.lookup_eq_none.mpr h_mem.1
    have h_not_in_vc2 : vc2.lookup r = none := by
      simp only [List.mem_toFinset, List.mem_append, not_or] at h_mem
      exact Std.AssocList.lookup_eq_none.mpr h_mem.2
    simp [h_not_in_vc1, h_not_in_vc2, Option.getD]
    -- 0 ≤ 0

-- | Helper lemma: If compareVectorClocks returns LT, then exists region where vc1 < vc2
lemma compareVectorClocks_LT_implies_lt (vc1 vc2 : VectorClock) :
  compareVectorClocks vc1 vc2 = VectorClockOrder.LT →
  ∃ r : String, VectorClock.get vc1 r < VectorClock.get vc2 r := by
  intro h_eq
  unfold compareVectorClocks at h_eq
  -- If compareVectorClocks returns LT, the condition vc1StrictLess must be true
  -- vc1StrictLess means allRegions.toList.any (fun r => vc1 r < vc2 r)
  -- List.any returns true iff ∃r ∈ allRegions, predicate holds
  --
  -- Extract the witness: when compareVectorClocks returns LT, vc1StrictLess = true
  -- This means List.any (fun r => VectorClock.get vc1 r < VectorClock.get vc2 r) = true
  -- By List.any_eq_true: ∃ r ∈ allRegions, VectorClock.get vc1 r < VectorClock.get vc2 r
  let allRegions := (vc1.keys ++ vc2.keys).toFinset.toList
  -- When the function returns LT, vc1StrictLess must be true (by the if-then-else structure)
  have h_strict : allRegions.any (fun r => decide (VectorClock.get vc1 r < VectorClock.get vc2 r)) = true := by
    -- LT is returned when: not (vc1Less && vc2Less) && vc1Less && vc1StrictLess
    -- From h_eq, we can extract that vc1StrictLess = true
    split at h_eq <;> simp_all
  -- Convert from List.any to existence
  have h_exists_in_list := List.any_eq_true.mp h_strict
  obtain ⟨r, h_r_mem, h_r_lt⟩ := h_exists_in_list
  exact ⟨r, of_decide_eq_true h_r_lt⟩

-- | Helper lemma: If compareVectorClocks returns LT, then vc2 is not ≤ vc1 everywhere
lemma compareVectorClocks_LT_implies_not_vc2_le (vc1 vc2 : VectorClock) :
  compareVectorClocks vc1 vc2 = VectorClockOrder.LT →
  ¬ (∀ r : String, VectorClock.get vc2 r ≤ VectorClock.get vc1 r) := by
  intro h_eq h_vc2_le
  -- If vc2 ≤ vc1 everywhere, then vc2Less would be true
  -- But if vc1Less && vc2Less, we'd return EQ, not LT
  -- Contradiction
  have h_lt := compareVectorClocks_LT_implies_lt vc1 vc2 h_eq
  cases h_lt with
  | intro r h_strict =>
    have h_le := h_vc2_le r
    -- Contradiction: vc1 r < vc2 r but vc2 r ≤ vc1 r
    linarith

-- | Theorem: Vector clock causal ordering
-- | If vc1 < vc2 (all regions in vc1 ≤ vc2, and at least one is strictly less),
-- | then vc1 happened before vc2
theorem vectorClock_causal_ordering (vc1 vc2 : VectorClock) :
  (∀ r : String, VectorClock.get vc1 r ≤ VectorClock.get vc2 r) →
  (∃ r : String, VectorClock.get vc1 r < VectorClock.get vc2 r) →
  happenedBefore vc1 vc2 := by
  -- If all regions in vc1 ≤ vc2 and at least one is strictly less,
  -- then compareVectorClocks returns LT
  intro h_all_le h_exists_lt
  unfold happenedBefore compareVectorClocks
  -- Show that the conditions for LT are met
  simp [h_all_le]
  -- Show vc1StrictLess is true (exists region where vc1 r < vc2 r)
  cases h_exists_lt with
  | intro r h_lt =>
    simp [h_lt]
    -- Show vc2Less is false (vc2 cannot be ≤ vc1 everywhere if vc1 < vc2 somewhere)
    -- If vc2Less were true, we'd have vc2 r ≤ vc1 r, but h_lt shows vc1 r < vc2 r
    intro h_vc2_le_all
    have h_vc2_le_r := h_vc2_le_all r
    -- Contradiction: vc1 r < vc2 r but vc2 r ≤ vc1 r
    linarith

-- | Theorem: Happened-before is transitive
-- | If vc1 happened before vc2, and vc2 happened before vc3, then vc1 happened before vc3
theorem happenedBefore_transitive (vc1 vc2 vc3 : VectorClock) :
  happenedBefore vc1 vc2 →
  happenedBefore vc2 vc3 →
  happenedBefore vc1 vc3 := by
  -- Transitivity follows from transitivity of ≤ and < on Nat
  intro h12 h23
  -- h12 means compareVectorClocks vc1 vc2 = LT
  -- This implies: ∀r, vc1 r ≤ vc2 r and ∃r, vc1 r < vc2 r
  -- h23 means compareVectorClocks vc2 vc3 = LT  
  -- This implies: ∀r, vc2 r ≤ vc3 r and ∃r, vc2 r < vc3 r
  -- Need to show: ∀r, vc1 r ≤ vc3 r and ∃r, vc1 r < vc3 r
  apply vectorClock_causal_ordering
  · -- Show ∀r, vc1 r ≤ vc3 r
    intro r
    -- From h12: vc1 r ≤ vc2 r (since compareVectorClocks returned LT)
    -- From h23: vc2 r ≤ vc3 r (since compareVectorClocks returned LT)
    -- Therefore vc1 r ≤ vc3 r by transitivity
    have h1 := compareVectorClocks_LT_implies_le vc1 vc2 h12
    have h2 := compareVectorClocks_LT_implies_le vc2 vc3 h23
    exact Nat.le_trans (h1 r) (h2 r)
  · -- Show ∃r, vc1 r < vc3 r
    -- Use transitivity: if vc1 r < vc2 r and vc2 r ≤ vc3 r, then vc1 r < vc3 r
    have h_strict12 := compareVectorClocks_LT_implies_lt vc1 vc2 h12
    have h_le23 := compareVectorClocks_LT_implies_le vc2 vc3 h23
    cases h_strict12 with
    | intro r h_lt =>
      -- vc1 r < vc2 r and vc2 r ≤ vc3 r, so vc1 r < vc3 r
      have h_le := h_le23 r
      exact ⟨r, Nat.lt_of_lt_of_le h_lt h_le⟩

-- | Theorem: Happened-before is irreflexive
-- | vc1 cannot happen before itself
theorem happenedBefore_irreflexive (vc1 : VectorClock) :
  ¬ happenedBefore vc1 vc1 := by
  -- A vector clock cannot be strictly less than itself
  unfold happenedBefore compareVectorClocks
  -- For compareVectorClocks vc1 vc1 to return LT, we'd need:
  -- vc1Less = true (all regions vc1 r ≤ vc1 r) ✓
  -- vc2Less = true (all regions vc1 r ≤ vc1 r) ✓
  -- vc1StrictLess = true (exists r, vc1 r < vc1 r) ✗
  -- But vc1Less && vc2Less means we return EQ, not LT
  -- Even if we somehow got LT, vc1StrictLess would require ∃r, vc1 r < vc1 r
  -- But Nat.lt_irrefl shows this is impossible
  intro h
  -- h means compareVectorClocks vc1 vc1 = LT
  -- This requires vc1StrictLess = true, meaning ∃r, vc1 r < vc1 r
  -- Contradiction
  have h_lt := compareVectorClocks_LT_implies_lt vc1 vc1 h
  cases h_lt with
  | intro r h_strict =>
    -- Contradiction: vc1 r < vc1 r is impossible
    exact Nat.lt_irrefl (VectorClock.get vc1 r) h_strict

-- | Theorem: Happened-before is asymmetric
-- | If vc1 happened before vc2, then vc2 did not happen before vc1
theorem happenedBefore_asymmetric (vc1 vc2 : VectorClock) :
  happenedBefore vc1 vc2 →
  ¬ happenedBefore vc2 vc1 := by
  -- If vc1 < vc2, then vc2 cannot be < vc1 (asymmetry of <)
  intro h12 h21
  -- h12: compareVectorClocks vc1 vc2 = LT means ∀r, vc1 r ≤ vc2 r and ∃r, vc1 r < vc2 r
  -- h21: compareVectorClocks vc2 vc1 = LT means ∀r, vc2 r ≤ vc1 r and ∃r, vc2 r < vc1 r
  -- Need to show contradiction
  -- From h12: ∃r1, vc1 r1 < vc2 r1, and ∀r, vc1 r ≤ vc2 r
  -- From h21: ∃r2, vc2 r2 < vc1 r2, and ∀r, vc2 r ≤ vc1 r
  -- For r2: vc2 r2 < vc1 r2 (from h21) but vc1 r2 ≤ vc2 r2 (from h12), contradiction
  have h_le12 := compareVectorClocks_LT_implies_le vc1 vc2 h12
  have h_strict21 := compareVectorClocks_LT_implies_lt vc2 vc1 h21
  cases h_strict21 with
  | intro r h_lt =>
    -- vc2 r < vc1 r (from h21) but vc1 r ≤ vc2 r (from h12)
    have h_le := h_le12 r
    -- Contradiction: vc2 r < vc1 r ≤ vc2 r
    linarith
