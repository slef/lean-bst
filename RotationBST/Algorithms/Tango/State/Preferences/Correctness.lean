module

public import RotationBST.Algorithms.Tango.State.Preferences.Local
public import RotationBST.Algorithms.Tango.State.Canonical.Local
public import RotationBST.Algorithms.Tango.Preferences.Updates.Validity

@[expose] public section
namespace RotationBST.Tango.MarkedTree

private theorem root_phase (l r : MarkedTree) (root lo : Nat) (size : l.tree.size = root)
    (previous : Option Bool) (next : Bool) :
    (match previous with
      | none => MarkedTree.node l r true true
      | some true => .node l r false true
      | some false => .node l r true false).applyFrom lo
        (if previous = some next then [] else [⟨lo + root, previous, next⟩]) =
      .node l r (!next) next := by
  cases previous with
  | none => cases next <;> simp [applyFrom, setPreference, size]
  | some old => cases old <;> cases next <;> simp [applyFrom, setPreference, size]

/-- The generated changes produce exactly the next reference marking, in the
subtree-local formulation used by the log generator. -/
theorem preferenceUpdates_local (t : Tree) (lo : Nat) (past : List Nat) (x : Nat)
    (valid : x < t.size) :
    (localCanonical t past).applyFrom lo (preferenceUpdates t lo past x) =
      localCanonical t (past ++ [x]) := by
  induction t generalizing lo past x with
  | nil => simp [Tree.size] at valid
  | node l r il ir =>
    have hv : x < l.size + 1 + r.size := valid
    have last : (regions l.size (l.size + 1 + r.size) (past ++ [x])).getLast? =
        some (decide (x ≤ l.size)) := by simp [regions, hv]
    have phase := root_phase (localCanonical l (leftRequests l.size past))
      (localCanonical r (rightRequests l.size past)) l.size lo (by simp)
      (regions l.size (l.size + 1 + r.size) past).getLast? (decide (x ≤ l.size))
    simp only [localCanonical, preferenceUpdates, ite_eq_left hv, applyFrom_append]
    erw [phase, last]
    by_cases hl : x < l.size
    · have hr : ¬ l.size < x := by omega
      have side : x ≤ l.size := by omega
      simp only [ite_eq_left hl, decide_eq_true side]
      rw [applyFrom_left]
      · rw [il lo _ x hl]
        simp [leftRequests, rightRequests, hl, hr]
      · intro e he
        simpa only [localCanonical_tree] using preferenceUpdates_bounds l lo (leftRequests l.size past) x e he
    · by_cases he : x = l.size
      · subst x
        simp [applyFrom, leftRequests, rightRequests]
      · have hr : l.size < x := by omega
        have subvalid : x - l.size - 1 < r.size := by omega
        have side : ¬ x ≤ l.size := by omega
        simp only [ite_eq_right hl, ite_eq_right he, decide_eq_false side]
        rw [applyFrom_right]
        · simp only [localCanonical_tree]
          rw [ir (lo + l.size + 1) _ _ subvalid]
          simp [leftRequests, rightRequests, hl, hr]
        · intro e member
          simpa only [localCanonical_tree] using
            (preferenceUpdates_bounds r (lo + l.size + 1) (rightRequests l.size past)
              (x - l.size - 1) e member).1

/-- Applying the generated log for one request exactly updates the canonical
reference marking, not merely its component-size or partition statistics. -/
theorem preferenceUpdates_canonical (t : Tree) (past : List Nat) (x : Nat)
    (history : ∀ y ∈ past, y < t.size) (valid : x < t.size) :
    (canonical t 0 past).applyPreferences (preferenceUpdates t 0 past x) =
      canonical t 0 (past ++ [x]) := by
  have extended : ∀ y ∈ past ++ [x], y < t.size := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact history y hy
    · have h := List.mem_singleton.mp hy
      simpa only [h] using valid
  rw [← localCanonical_eq t past history, ← applyFrom_zero,
    preferenceUpdates_local t 0 past x valid, localCanonical_eq t (past ++ [x]) extended]

theorem applyPreferences_append (s : MarkedTree) (xs ys : List PreferenceUpdate) :
    s.applyPreferences (xs ++ ys) = (s.applyPreferences xs).applyPreferences ys := by
  simpa only [applyFrom_zero] using applyFrom_append s 0 xs ys

/-- The complete causal log realizes the canonical marking of the complete
history. Later accesses can be interleaved without changing this specification. -/
theorem preferenceLog_canonical (t : Tree) (past xs : List Nat)
    (history : ∀ y ∈ past, y < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    (canonical t 0 past).applyPreferences (preferenceLog t past xs) =
      canonical t 0 (past ++ xs) := by
  induction xs generalizing past with
  | nil => simp [preferenceLog, applyPreferences]
  | cons x xs ih =>
    have hx := valid x (List.mem_cons_self ..)
    have extended : ∀ y ∈ past ++ [x], y < t.size := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact history y hy
      · have h := List.mem_singleton.mp hy
        simpa only [h] using hx
    rw [preferenceLog, applyPreferences_append, preferenceUpdates_canonical t past x history hx]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (past ++ [x]) extended (fun y hy => valid y (List.mem_cons_of_mem _ hy))

end RotationBST.Tango.MarkedTree
