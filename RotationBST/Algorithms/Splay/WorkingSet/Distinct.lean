module

public import RotationBST.Algorithms.Splay.WorkingSet.Recency
public import RotationBST.Bounds.WorkingSet.Abstract

@[expose] public section

namespace RotationBST.Recency

variable {x : Nat}

theorem nodup_eraseDups (xs : List Nat) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons x xs =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp [List.mem_eraseDups, List.mem_filter]
      · exact nodup_eraseDups (xs.filter fun y => !y == x)
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

theorem eraseDups_eq_self (xs : List Nat) (hn : xs.Nodup) : xs.eraseDups = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨hx, hn⟩ := List.nodup_cons.mp hn
      have hf : xs.filter (fun y => !y == x) = xs := by
        apply List.filter_eq_self.mpr
        intro y hy
        have : y ≠ x := by intro he; subst y; exact hx hy
        simpa using this
      rw [List.eraseDups_cons, hf, ih hn]

theorem eraseDups_filter (p : Nat → Bool) (xs : List Nat) :
    (xs.filter p).eraseDups = xs.eraseDups.filter p := by
  cases xs with
  | nil => simp
  | cons x xs =>
      by_cases hx : p x = true
      · rw [List.filter_cons_of_pos hx, List.eraseDups_cons, List.eraseDups_cons,
          List.filter_cons_of_pos hx]
        rw [List.filter_comm, eraseDups_filter p (xs.filter fun y => !y == x)]
      · rw [List.filter_cons_of_neg hx, List.eraseDups_cons, List.filter_cons_of_neg hx,
          ← eraseDups_filter p (xs.filter fun y => !y == x)]
        congr 1
        rw [List.filter_filter]
        apply List.filter_congr
        intro y _
        by_cases hy : y = x
        · subst y; simp [hx]
        · simp [hy]
termination_by xs.length
decreasing_by all_goals exact Nat.lt_succ_of_le (List.length_filter_le ..)

theorem eraseDups_cons_touch (x : Nat) (xs : List Nat) :
    (x :: xs).eraseDups = touch xs.eraseDups x := by
  rw [List.eraseDups_cons, eraseDups_filter]
  rw [touch, (nodup_eraseDups xs).erase_eq_filter]
  rfl

/-- The most recent occurrence comes first; previously unseen keys retain their
initial sorted order. This is always a permutation of the key universe. -/
def recent (n : Nat) (past : List Nat) : List Nat := (past.reverse ++ List.range n).eraseDups

theorem recent_nil (n : Nat) : recent n [] = List.range n := by
  simp only [recent, List.reverse_nil, List.nil_append]
  exact eraseDups_eq_self _ List.nodup_range

theorem recent_step (n x : Nat) (past : List Nat) :
    recent n (past ++ [x]) = touch (recent n past) x := by
  simp only [recent, List.reverse_append, List.reverse_singleton, List.nil_append,
    List.cons_append, eraseDups_cons_touch]

theorem recent_perm (n : Nat) (past : List Nat) (hv : ∀ x ∈ past, x < n) :
    (recent n past).Perm (List.range n) := by
  apply (List.perm_ext_iff_of_nodup (nodup_eraseDups _) List.nodup_range).mpr
  intro x
  simp only [List.mem_eraseDups, List.mem_append, List.mem_reverse, List.mem_range]
  exact ⟨fun h => h.elim (hv x) id, Or.inr⟩

theorem first_split (xs : List Nat) (hx : x ∈ xs) :
    ∃ pre post, xs = pre ++ x :: post ∧ x ∉ pre ∧ xs.takeWhile (· != x) = pre := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
      by_cases he : a = x
      · subst a
        exact ⟨[], xs, rfl, by simp, by simp⟩
      · have hx' : x ∈ xs := (List.mem_cons.mp hx).resolve_left (Ne.symm he)
        obtain ⟨pre, post, hs, hp, ht⟩ := ih hx'
        refine ⟨a :: pre, post, by simp [hs], by simp [hp, Ne.symm he], ?_⟩
        simp [he, ht]

theorem idxOf_eraseDups_split (pre post : List Nat) (hx : x ∉ pre) :
    (pre ++ x :: post).eraseDups.idxOf x = pre.eraseDups.length := by
  rw [List.eraseDups_append, List.idxOf_append, ite_eq_right (by simpa [List.mem_eraseDups] using hx)]
  simp [List.removeAll, hx, List.eraseDups_cons]

/-- Recency position equals the working-set number on repeat accesses, and is
at most the universe size on first access. -/
theorem rank_le_workingSet (n x : Nat) (past : List Nat)
    (hv : ∀ y ∈ past, y < n) (hx : x < n) :
    (recent n past).idxOf x + 1 ≤ workingSetNumber n past x := by
  by_cases hm : x ∈ past
  · obtain ⟨pre, post, hs, hp, ht⟩ := first_split past.reverse (by simpa using hm)
    have hi : (recent n past).idxOf x = pre.eraseDups.length := by
      simp only [recent, hs, List.append_assoc, List.cons_append]
      exact idxOf_eraseDups_split pre (post ++ List.range n) hp
    simp only [workingSetNumber, ite_eq_left hm, ht, hi]
    omega
  · have hp := recent_perm n past hv
    have hx' : x ∈ recent n past := hp.mem_iff.mpr (List.mem_range.mpr hx)
    have hi := List.idxOf_lt_length_of_mem hx'
    have hl : (recent n past).length = n := hp.length_eq.trans List.length_range
    simp only [workingSetNumber, ite_eq_right hm]
    omega

end RotationBST.Recency
