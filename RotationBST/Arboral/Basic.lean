module

public import RotationBST.Arboral.Definitions.Abstract
import Mathlib.Data.Set.Finite.Lemmas

@[expose] public section
namespace RotationBST.Arboral

@[simp] theorem mem_row (p : Point) (time : Nat) (keys : Finset Nat) :
    p ∈ row time keys ↔ p.1 ∈ keys ∧ p.2 = time := by
  rcases p with ⟨x, y⟩
  simp [row, eq_comm]

theorem rectangle_symm (a b p : Point) : Rectangle a b p ↔ Rectangle b a p := by
  simp [Rectangle, min_comm, max_comm]

theorem ass_empty : ASS ∅ := by simp [ASS]

theorem ass_row (time : Nat) (keys : Finset Nat) : ASS (row time keys) := by
  intro a ha b hb _ h
  exact (h ((mem_row a time keys).mp ha |>.2.trans
    ((mem_row b time keys).mp hb |>.2.symm))).elim

/-- Cutting off future rows preserves satisfaction. Arbitrary subsets need not. -/
theorem ass_prefix {P : Finset Point} (h : ASS P) (time : Nat) :
    ASS (P.filter fun p => p.2 < time) := by
  intro a ha b hb hx hy
  obtain ⟨ha, hat⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb, hbt⟩ := Finset.mem_filter.mp hb
  obtain ⟨p, hp, hpa, hpb, hr⟩ := h a ha b hb hx hy
  exact ⟨p, Finset.mem_filter.mpr ⟨hp, lt_of_le_of_lt hr.2.2.2
    (max_lt hat hbt)⟩, hpa, hpb, hr⟩

/-- Touching every key on a new row is always a legal completion. -/
theorem full_row {n time request : Nat} {P : Finset Point}
    (hist : History n time P) (sat : ASS P) (valid : request < n) :
    Completion n time request P (Finset.range n) := by
  refine ⟨Finset.mem_range.mpr valid, fun _ h => h, ?_⟩
  have cross : ∀ a ∈ P, ∀ b ∈ row time (Finset.range n), a.1 ≠ b.1 →
      ∃ p ∈ P ∪ row time (Finset.range n), p ≠ a ∧ p ≠ b ∧ Rectangle a b p := by
    intro a ha b hb hx
    obtain ⟨_, hbt⟩ := (mem_row b time _).mp hb
    obtain ⟨han, hat⟩ := hist a ha
    refine ⟨(a.1, time), Finset.mem_union_right _ ?_, ?_, ?_, ?_⟩
    · simp [mem_row, han]
    · intro heq
      have := congrArg Prod.snd heq
      simp only at this
      omega
    · intro heq
      apply hx
      have h := congrArg (fun p : Point => p.1) heq
      exact h
    · simp only [Rectangle]
      subst hbt
      exact ⟨min_le_left _ _, le_max_left _ _, min_le_right _ _, le_max_right _ _⟩
  intro a ha b hb hx hy
  rcases Finset.mem_union.mp ha with ha | ha <;>
    rcases Finset.mem_union.mp hb with hb | hb
  · obtain ⟨p, hp, hpa, hpb, hr⟩ := sat a ha b hb hx hy
    exact ⟨p, Finset.mem_union_left _ hp, hpa, hpb, hr⟩
  · exact cross a ha b hb hx
  · obtain ⟨p, hp, hpb, hpa, hr⟩ := cross b hb a ha (Ne.symm hx)
    exact ⟨p, hp, hpa, hpb, (rectangle_symm b a p).mp hr⟩
  · exact (hy (((mem_row a time _).mp ha).2.trans
      ((mem_row b time _).mp hb).2.symm)).elim

theorem greedy_exists {n time request : Nat} {P : Finset Point}
    (hist : History n time P) (sat : ASS P) (valid : request < n) :
    ∃ keys, GreedyRow n time request P keys := by
  classical
  let S : Set (Finset Nat) := {keys : Finset Nat | Completion n time request P keys}
  have finite : S.Finite := (Finset.finite_toSet (Finset.range n).powerset).subset
    (by intro keys hk; exact Finset.mem_powerset.mpr hk.2.1)
  obtain ⟨keys, hk, hmin⟩ := Set.exists_min_image S Finset.card finite
    ⟨Finset.range n, full_row hist sat valid⟩
  exact ⟨keys, hk, hmin⟩

theorem completion_card {n time request : Nat} {P : Finset Point} {keys : Finset Nat}
    (hist : History n time P) (_h : Completion n time request P keys) :
    (P ∪ row time keys).card = P.card + keys.card := by
  have dis : Disjoint P (row time keys) := by
    rw [Finset.disjoint_left]
    intro p hp hr
    have := (hist p hp).2
    have := ((mem_row p time keys).mp hr).2
    omega
  rw [Finset.card_union_of_disjoint dis]
  congr 1
  exact Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

end RotationBST.Arboral
