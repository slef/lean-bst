module

public import RotationBST.Tango.Preferences.Updates.Abstract
public import RotationBST.Tango.Preferences.Proofs

@[expose] public section
namespace RotationBST.Tango

theorem runs_append (xs : List Bool) (x : Bool) :
    runs (xs ++ [x]) = runs xs + if xs.getLast? = some x then 0 else 1 := by
  rw [runs_eq, runs_eq, alternations_append]
  cases xs with
  | nil => simp [switch]
  | cons a xs =>
    have hn : (a :: xs).getLast? ≠ none := by simp
    cases h : (a :: xs).getLast? with
    | none => exact False.elim (hn h)
    | some b =>
      simp only [switch, h, List.cons_ne_nil, ite_false, List.append_eq_nil_iff,
        false_and, Option.some.injEq]
      omega

/-- The executable log counts exactly the newly initialized or changed labels. -/
theorem preferenceUpdates_count (t : Tree) (lo : Nat) (past : List Nat) (x : Nat)
    (valid : x < t.size) :
    preferenceChanges t (past ++ [x]) = preferenceChanges t past + (preferenceUpdates t lo past x).length := by
  induction t generalizing lo past x with
  | nil => simp [Tree.size] at valid
  | node l r il ir =>
    have hv : x < l.size + 1 + r.size := valid
    simp only [preferenceChanges, preferenceUpdates, ite_eq_left hv, regions_append, left_append, right_append]
    have region : regions l.size (l.size + 1 + r.size) [x] = [decide (x ≤ l.size)] := by
      simp [regions, hv]
    rw [region, runs_append]
    have rootLength (p : Option Bool) (b : Bool) :
        (if p = some b then [] else [PreferenceUpdate.mk (lo + l.size) p b]).length =
          if p = some b then 0 else 1 := by split <;> rfl
    rw [List.length_append, rootLength]
    by_cases hl : x < l.size
    · have hr : ¬ l.size < x := by omega
      simp only [leftRequests, rightRequests, List.filter_cons, decide_eq_true_eq,
        hl, hr, ↓reduceIte, List.filter_nil, List.map_nil, List.append_nil]
      have hrec := il lo (leftRequests l.size past) x hl
      simp only [leftRequests] at hrec
      omega
    · by_cases he : x = l.size
      · subst x
        simp [leftRequests, rightRequests, Nat.add_assoc, Nat.add_comm]
      · have hr : l.size < x := by omega
        have hv' : x - l.size - 1 < r.size := by omega
        simp only [leftRequests, rightRequests, List.filter_cons, decide_eq_true_eq,
          hl, hr, ↓reduceIte, List.filter_nil, List.map_nil, List.append_nil,
          List.map_cons, ite_eq_right he]
        have hrec := ir (lo + l.size + 1) (rightRequests l.size past) (x - l.size - 1) hv'
        simp only [rightRequests] at hrec
        omega

theorem preferenceLog_count (t : Tree) (past xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    preferenceChanges t (past ++ xs) = preferenceChanges t past + (preferenceLog t past xs).length := by
  induction xs generalizing past with
  | nil => simp [preferenceLog]
  | cons x xs ih =>
    have hx := preferenceUpdates_count t 0 past x (valid x (List.mem_cons_self ..))
    have h := ih (past ++ [x]) (fun y hy => valid y (List.mem_cons_of_mem _ hy))
    simpa only [preferenceLog, List.length_append, List.append_assoc, List.cons_append,
      List.nil_append, hx, Nat.add_assoc] using h

theorem preferenceChanges_nil (t : Tree) : preferenceChanges t [] = 0 := by
  induction t with
  | nil => rfl
  | node l r il ir => simp [preferenceChanges, regions, leftRequests, rightRequests, runs, il, ir]

theorem preferenceLog_bound (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    (preferenceLog t [] xs).length ≤ interleave t xs + t.size := by
  have counts := preferenceLog_count t [] xs valid
  simp only [List.nil_append, preferenceChanges_nil, Nat.zero_add] at counts
  rw [← counts]
  exact preferenceChanges_bound t xs

/-- Extending the request sequence appends updates without changing its prefix. -/
theorem preferenceLog_append (t : Tree) (past xs ys : List Nat) :
    preferenceLog t past (xs ++ ys) = preferenceLog t past xs ++ preferenceLog t (past ++ xs) ys := by
  induction xs generalizing past with
  | nil => simp [preferenceLog]
  | cons x xs ih => simp [preferenceLog, ih, List.append_assoc]

end RotationBST.Tango
