-- | Lean4 proofs for Forge Session invariants
-- | Phase 2: Type Safety Layer
import Lean

namespace Forge.Proofs.Session

-- | Session ID structure (non-empty string)
structure SessionID where
  value : String
  nonEmpty : value.length > 0

-- | Session time structure with ordering invariant
structure SessionTime where
  created : Nat
  updated : Nat
  ordered : created ≤ updated

-- | Session summary with non-negative invariants
structure SessionSummary where
  additions : Nat
  deletions : Nat
  files : Nat
  nonNegative : additions ≥ 0 ∧ deletions ≥ 0 ∧ files ≥ 0

-- | Session ID is never empty (by construction)
theorem sessionIdNonEmpty (id : SessionID) : id.value.length > 0 :=
  id.nonEmpty

-- | Session time.created <= time.updated (by construction)
theorem sessionTimeOrdered (time : SessionTime) : 
  time.created ≤ time.updated :=
  time.ordered

-- | Session summary additions + deletions >= 0 (by construction)
theorem sessionSummaryNonNegative (summary : SessionSummary) :
  summary.additions ≥ 0 ∧ summary.deletions ≥ 0 ∧ summary.files ≥ 0 :=
  summary.nonNegative

-- | Session with parentID must have valid parent reference
-- | Store invariant: all parentIDs reference valid sessions
structure SessionStore where
  sessions : List SessionID
  parentMap : SessionID → Option SessionID
  -- Invariant: all parentIDs in parentMap reference sessions that exist in sessions list
  parentInvariant : ∀ (sid : SessionID), 
    (match parentMap sid with
     | some parentID => ∃ parent, parent.id = parentID ∧ parent ∈ sessions
     | none => True)

structure Session where
  id : SessionID
  parentID : Option SessionID

-- | Theorem: Session parentID is valid when it matches store state
-- | This theorem requires that the session structure matches the store's parentMap.
-- | This is a runtime invariant that must be maintained by the store implementation.
theorem sessionParentValid (store : SessionStore) (session : Session) 
  (hConsistency : session.parentID = store.parentMap session.id) :
  (session.parentID.isSome → ∃ parent, parent.id = session.parentID.get ∧ parent ∈ store.sessions) := by
  intro h
  cases h with
  | some parentID =>
    -- Use the consistency assumption
    rw [hConsistency] at h
    -- Now h says: (parentMap session.id).isSome = true
    -- Use the store's parent invariant
    have hInvariant := store.parentInvariant session.id
    -- The invariant guarantees that if parentMap session.id = some parentID,
    -- then parent exists in sessions
    -- We need to extract the parentID from the match
    cases store.parentMap session.id with
    | none => 
      -- If parentMap session.id = none, then (parentMap session.id).isSome = false
      -- But h says it's true, contradiction
      simp at h
    | some pid =>
      -- Now we have parentMap session.id = some pid
      -- And from hConsistency, session.parentID = some pid
      -- So parentID = pid
      have hEq : parentID = pid := by
        rw [← hConsistency] at h
        injection h
      rw [hEq]
      -- Use the invariant: parentMap session.id = some pid → ∃ parent, parent.id = pid ∧ parent ∈ sessions
      exact hInvariant
  | none =>
    -- If parentID is None, the implication is vacuously true
    trivial

-- | All sessions in store have valid parent references
theorem allSessionsHaveValidParents (store : SessionStore) :
  ∀ session ∈ store.sessions, 
    (match store.parentMap session.id with
     | some parentID => ∃ parent, parent.id = parentID ∧ parent ∈ store.sessions
     | none => True) := by
  intro session hIn
  -- Use the store's parent invariant directly
  exact store.parentInvariant session.id

end Forge.Proofs.Session
