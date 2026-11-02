module

public import RotationBST.Arboral.Basic

@[expose] public section
namespace RotationBST.Arboral

theorem mem_subsets (n : Nat) (keys : Finset Nat) :
    keys ∈ subsets n ↔ keys ⊆ Finset.range n := by
  induction n generalizing keys with
  | zero => simp [subsets]
  | succ n ih =>
    simp only [subsets, List.mem_append, List.mem_map, ih]
    constructor
    · rintro (h | ⟨s, hs, rfl⟩)
      · exact h.trans (Finset.range_mono (Nat.le_succ n))
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simp
        · exact Finset.range_mono (Nat.le_succ n) (hs hx)
    · intro h
      by_cases hn : n ∈ keys
      · right
        refine ⟨keys.erase n, ?_, Finset.insert_erase hn⟩
        intro x hx
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hx
        have hlt := Finset.mem_range.mp (h hmem)
        exact Finset.mem_range.mpr (by omega)
      · left
        intro x hx
        have hlt := Finset.mem_range.mp (h hx)
        have hne : x ≠ n := by rintro rfl; exact hn hx
        exact Finset.mem_range.mpr (by omega)

private theorem fold_valid (Q : Finset Nat → Prop) (xs : List (Finset Nat))
    (all : ∀ x ∈ xs, Q x) (a : Finset Nat) (ha : Q a) :
    Q (xs.foldl smaller a) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons b bs ih =>
    apply ih (fun x hx => all x (List.mem_cons_of_mem _ hx))
    unfold smaller
    split
    · exact all b (List.mem_cons_self ..)
    · exact ha

private theorem fold_le_start (xs : List (Finset Nat)) (a : Finset Nat) :
    (xs.foldl smaller a).card ≤ a.card := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons b bs ih =>
    apply (ih (smaller a b)).trans
    unfold smaller
    split <;> rename_i h
    · exact Nat.le_of_lt h
    · exact le_rfl

private theorem fold_le_member (xs : List (Finset Nat)) (a b : Finset Nat)
    (hb : b ∈ xs) : (xs.foldl smaller a).card ≤ b.card := by
  induction xs generalizing a with
  | nil => simp at hb
  | cons c cs ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · apply (fold_le_start cs (smaller a b)).trans
      unfold smaller
      split
      · exact le_rfl
      · omega
    · exact ih (smaller a c) hb

theorem greedy_correct {n time request : Nat} {P : Finset Point}
    (hist : History n time P) (sat : ASS P) (valid : request < n) :
    GreedyRow n time request P (greedy n time request P) := by
  constructor
  · apply fold_valid (Completion n time request P)
    · intro x hx
      exact of_decide_eq_true (List.mem_filter.mp hx).2
    · exact full_row hist sat valid
  · intro other ho
    apply fold_le_member
    exact List.mem_filter.mpr ⟨(mem_subsets n other).mpr ho.2.1, by simpa using ho⟩

end RotationBST.Arboral
