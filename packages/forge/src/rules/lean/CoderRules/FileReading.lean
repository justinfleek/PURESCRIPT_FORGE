-- | File reading protocol - proofs in Lean4
import Mathlib.Data.List.Basic
import Mathlib.Data.List.SplitOn
import Mathlib.Data.String.Basic
import Mathlib.Tactic

namespace PureScriptForgeRules

open String

-- | File reading protocol:
-- | GREP IS BANNED
-- | HEAD/TAIL IS BANNED
-- | PARTIAL READS ARE BANNED
-- | SEARCH PATTERNS ARE BANNED
-- | "RELEVANT SECTIONS" ARE BANNED

-- | Complete file read result
structure FileReadResult where
  filePath : String
  content : String
  lineCount : Nat
  deriving Repr

-- | Chunk file into segments
-- | Each chunk is ≤500 lines
def chunkFile (content : String) (chunkSize : Nat := 500) : List String :=
  let lines := content.splitOn "\n"
  in lines.chunk chunkSize |>.map (String.intercalate "\n")

-- | Helper lemma: chunk preserves content when joined
private theorem chunk_join_preserves_content {α : Type} (xs : List α) (n : Nat) :
  (xs.chunk n).join = xs := by
  induction xs with
  | nil => 
    simp [List.chunk, List.join]
  | cons x xs ih =>
    cases n with
    | zero => 
      simp [List.chunk, List.join]
    | succ n =>
      simp [List.chunk]
      rw [List.join_append]
      rw [ih]
      rw [List.take_append_drop]

-- | Helper lemma: String.splitOn converts to List.splitOn
private theorem string_splitOn_toList (s sep : String) :
  s.splitOn sep = (s.toList.splitOn sep.toList).map String.ofList := by
  rfl

-- | Helper lemma: String.intercalate converts to List.intercalate
private theorem string_intercalate_toList (sep : String) (lines : List String) :
  String.intercalate sep lines = String.ofList (List.intercalate sep.toList (lines.map String.toList)) := by
  rfl

-- | Helper lemma: intercalate and splitOn are inverse operations
private theorem intercalate_splitOn_inverse (s : String) (sep : String) :
  String.intercalate sep (s.splitOn sep) = s := by
  rw [string_splitOn_toList s sep]
  rw [string_intercalate_toList sep ((s.toList.splitOn sep.toList).map String.ofList)]
  have h_map : ((s.toList.splitOn sep.toList).map String.ofList).map String.toList = s.toList.splitOn sep.toList := by
    rw [List.map_map]
    simp [Function.comp]
    rw [List.map_id]
    congr 1
    ext l
    exact String.toList_ofList l
  rw [h_map]
  rw [List.intercalate_splitOn]
  rw [String.ofList_toList]

-- | Theorem: Chunking preserves content
theorem chunkPreservesContent (content : String) (chunkSize : Nat) :
  (chunkFile content chunkSize).join = content := by
  unfold chunkFile
  simp [List.join_map]
  rw [chunk_join_preserves_content]
  exact intercalate_splitOn_inverse content "\n"

-- | Helper lemma: List.take produces length ≤ n
private theorem take_length_le {α : Type} (xs : List α) (n : Nat) :
  (xs.take n).length ≤ n := by
  induction xs generalizing n with
  | nil =>
    simp [List.take]
  | cons x xs ih =>
    cases n with
    | zero =>
      simp [List.take]
    | succ n =>
      simp [List.take]
      exact Nat.succ_le_succ (ih n)

-- | Helper lemma: chunk length bound
private theorem chunk_length_bound {α : Type} (xs : List α) (n : Nat) :
  ∀ chunk ∈ xs.chunk n, chunk.length ≤ n := by
  intro chunk hchunk
  induction xs with
  | nil =>
    simp [List.chunk] at hchunk
    contradiction
  | cons x xs ih =>
    cases n with
    | zero =>
      simp [List.chunk] at hchunk
      contradiction
    | succ n =>
      simp [List.chunk] at hchunk
      cases hchunk with
      | inl h_first =>
        rw [h_first]
        exact take_length_le (x :: xs) (n + 1)
      | inr h_rest =>
        exact ih chunk h_rest

-- | Helper lemma: chunk preserves membership
-- | If group ∈ xs.chunk n and x ∈ group, then x ∈ xs
-- | This follows from the definition: chunk groups elements from xs using take/drop
private theorem chunk_preserves_membership {α : Type} (xs : List α) (n : Nat) :
  ∀ group ∈ xs.chunk n, ∀ x ∈ group, x ∈ xs := by
  intro group hgroup x hx
  -- Proof by induction on xs
  -- Base: [].chunk n = [], so no groups (contradiction)
  -- Step: (y :: ys).chunk n
  --   If n = 0: chunk produces [], so contradiction
  --   If n > 0: chunk produces [take n (y :: ys)] ++ chunk n (drop n (y :: ys))
  --     If group = take n (y :: ys): x ∈ take n (y :: ys) ⊆ y :: ys, so x ∈ y :: ys
  --     If group ∈ chunk n (drop n (y :: ys)): by IH, x ∈ drop n (y :: ys) ⊆ y :: ys, so x ∈ y :: ys
  induction xs with
  | nil =>
    simp [List.chunk] at hgroup
    contradiction
  | cons y ys ih =>
    cases n with
    | zero =>
      simp [List.chunk] at hgroup
      contradiction
    | succ n =>
      simp [List.chunk] at hgroup
      cases hgroup with
      | inl h_first =>
        -- group = take (n+1) (y :: ys)
        rw [h_first] at hx
        -- x ∈ take (n+1) (y :: ys)
        -- take produces a prefix, so x ∈ y :: ys
        have h_take_mem : ∀ x ∈ (y :: ys).take (n + 1), x ∈ y :: ys := by
          intro x' hx'
          -- take produces a prefix, so all elements are in the original list
          -- This follows from List.take_subset
          have h_subset : (y :: ys).take (n + 1) ⊆ y :: ys := List.take_subset (n + 1) (y :: ys)
          exact h_subset hx'
        exact h_take_mem x hx
      | inr h_rest =>
        -- group ∈ chunk (n+1) (drop (n+1) (y :: ys))
        -- By IH: x ∈ drop (n+1) (y :: ys)
        -- And drop produces a suffix, so x ∈ y :: ys
        have h_drop_mem : ∀ x ∈ (y :: ys).drop (n + 1), x ∈ y :: ys := by
          intro x' hx'
          -- drop produces a suffix, so all elements are in the original list
          -- This follows from List.drop_subset
          have h_subset : (y :: ys).drop (n + 1) ⊆ y :: ys := List.drop_subset (n + 1) (y :: ys)
          exact h_subset hx'
        have hx_drop : x ∈ (y :: ys).drop (n + 1) := ih group h_rest x hx
        exact h_drop_mem x hx_drop

-- | Helper lemma: intercalate preserves splitOn length
private theorem intercalate_splitOn_length (lines : List String) (sep : String)
  (h_no_sep : ∀ line ∈ lines, sep.toList ⊆ line.toList → False) :
  (String.intercalate sep lines).splitOn sep = lines := by
  rw [string_intercalate_toList sep lines]
  have h_split : (String.ofList (List.intercalate sep.toList (lines.map String.toList))).splitOn sep =
    ((List.intercalate sep.toList (lines.map String.toList)).splitOn sep.toList).map String.ofList := by
    rw [string_splitOn_toList]
    rw [String.toList_ofList]
  rw [h_split]
  cases lines with
  | nil =>
    simp [List.intercalate, List.splitOn]
  | cons line0 lines' =>
    have h_ne_nil : lines.map String.toList ≠ [] := by
      simp [List.map]
    have h_no_sep_list : ∀ l ∈ lines.map String.toList, sep.toList ⊆ l → False := by
      intro l h_mem h_subset
      obtain ⟨line, h_line_mem, h_eq⟩ := List.mem_map.mp h_mem
      rw [← h_eq] at h_subset
      exact h_no_sep line h_line_mem h_subset
    rw [List.splitOn_intercalate sep.toList (lines.map String.toList) h_no_sep_list h_ne_nil]
    rw [List.map_map]
    congr 1
    ext line
    exact String.ofList_toList line

-- | Helper: splitOn removes separator from results  
-- | If l ∈ xs.splitOn sep, then sep doesn't appear in l
-- | Proof: By induction on xs
-- | Base: [].splitOn sep = [[]], and sep ∉ [] (trivially)
-- | Step: (x :: xs).splitOn sep
-- |   If x == sep: produces [] :: xs.splitOn sep
-- |     [] doesn't contain sep, and by IH xs.splitOn sep results don't contain sep
-- |   If x ≠ sep: modifies head by cons x
-- |     By IH, original results don't contain sep, and x ≠ sep, so modified results don't contain sep
private theorem splitOn_removes_separator {α : Type} [DecidableEq α] (xs : List α) (sep : α) :
  ∀ l ∈ xs.splitOn sep, sep ∉ l := by
  induction xs with
  | nil =>
    simp [List.splitOn]
    intro l h_mem
    have : l = [] := by simp [List.splitOn] at h_mem; exact h_mem
    rw [this]
    simp
  | cons x xs ih =>
    simp [List.splitOn]
    intro l h_mem
    by_cases h_eq : x == sep
    · -- x == sep: splitOn produces [] :: xs.splitOn sep
      simp [h_eq] at h_mem
      cases h_mem with
      | inl h_empty =>
        rw [h_empty]
        simp
      | inr h_tail =>
        exact ih l h_tail
    · -- x ≠ sep: splitOn modifies head by cons x
      push_neg at h_eq
      -- modifyHead (cons x) prepends x to first element
      -- Need to extract structure: modifyHead f [h :: t] = [f h :: t]
      -- So l is either x :: h (where h is head of xs.splitOn sep) or from tail
      cases h_split : xs.splitOn sep with
      | nil =>
        have : xs.splitOn sep ≠ [] := List.splitOn_ne_nil sep xs
        contradiction
      | cons h t =>
        -- xs.splitOn sep = h :: t
        -- modifyHead (cons x) produces (x :: h) :: t
        simp [List.splitOn, h_eq] at h_mem
        simp [List.modifyHead, h_split] at h_mem
        cases h_mem with
        | inl h_eq_l =>
          -- l = x :: h
          rw [h_eq_l]
          intro h_sep
          cases h_sep with
          | head => contradiction  -- x = sep, but x ≠ sep
          | tail h_sep_h =>
            -- sep ∈ h, but h ∈ xs.splitOn sep, so by IH sep ∉ h
            have h_mem_h : h ∈ xs.splitOn sep := by rw [h_split]; simp
            exact ih h h_mem_h h_sep_h
        | inr h_tail_mem =>
          -- l ∈ t (tail of xs.splitOn sep)
          -- t is tail, so l ∈ xs.splitOn sep
          have h_mem_l : l ∈ xs.splitOn sep := by rw [h_split]; simp; exact h_tail_mem
          exact ih l h_mem_l

-- | Helper: Lines don't contain newline separator
private theorem lines_no_newline (content : String) :
  ∀ line ∈ content.splitOn "\n", ("\n".toList ⊆ line.toList → False) := by
  intro line h_mem
  obtain ⟨l, h_l_mem, h_line_eq⟩ := List.mem_map.mp (string_splitOn_toList content "\n" ▸ h_mem)
  have h_no_sep : '\n' ∉ l := splitOn_removes_separator (content.toList) '\n' l h_l_mem
  intro h_subset
  have h_mem_sep : '\n' ∈ l := by
    have h_singleton_subset : ∀ {x : Char} {l : List Char}, [x] ⊆ l → x ∈ l := by
      intro x l h_sub
      simp [List.subset_def] at h_sub
      exact h_sub x (by simp)
    exact h_singleton_subset h_subset
  exact h_no_sep h_mem_sep

-- | Theorem: All chunks are ≤ chunkSize
theorem chunkSizeBound (content : String) (chunkSize : Nat) :
  ∀ chunk ∈ chunkFile content chunkSize, (chunk.splitOn "\n").length ≤ chunkSize := by
  unfold chunkFile
  intro chunk hchunk
  obtain ⟨group, hgroup_mem, hchunk_eq⟩ := List.mem_map.mp hchunk
  rw [← hchunk_eq]
  have h_no_sep_group : ∀ line ∈ group, ("\n".toList ⊆ line.toList → False) := by
    intro line h_line_mem
    -- line is in group, and group is in (splitOn "\n" content).chunk chunkSize
    -- So line is in splitOn "\n" content (by chunk_preserves_membership)
    have h_line_in_split : line ∈ content.splitOn "\n" := 
      chunk_preserves_membership (content.splitOn "\n") chunkSize group hgroup_mem line h_line_mem
    -- Therefore line doesn't contain "\n" (by lines_no_newline)
    exact lines_no_newline content line h_line_in_split
  rw [intercalate_splitOn_length group "\n" h_no_sep_group]
  exact chunk_length_bound (content.splitOn "\n") chunkSize group hgroup_mem
