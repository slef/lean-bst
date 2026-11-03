module

public import RotationBST.Models.Geometric.Rectangle
public import RotationBST.Algorithms.GreedyASS.Greedy

import Mathlib.Tactic.Push

@[expose] public section
namespace RotationBST.Arboral

theorem sweep_subset {n time request : Nat} {P : Finset Point} {keys : Finset Nat}
    (hist : History n time P) (completion : Completion n time request P keys) :
    greedySweep time request P ⊆ keys := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact completion.1
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hq, hvisible⟩ := Finset.mem_filter.mp hq
  have req : (request, time) ∈ P ∪ row time keys :=
    Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨completion.1, rfl⟩)
  obtain ⟨p, hp, hpq, _, hrect, hside⟩ := side_witness completion.2.2
    (Finset.mem_union_left _ hq) req hvisible.1 (by have := (hist q hq).2; omega)
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (hvisible.2 p hp hpq hrect).elim
  obtain ⟨hkey, htime⟩ := (mem_row p time keys).mp hp
  rcases hside with hside | hside
  · simpa only [hside] using hkey
  · have := (hist q hq).2
    omega

private theorem projection {P : Finset Point} {time : Nat} {a b : Point}
    {keys : Finset Nat} (ha : a.2 < time) (hb : b.2 = time)
    (hx : a.1 ≠ b.1) (hkey : a.1 ∈ keys) :
    ∃ p ∈ P ∪ row time keys, p ≠ a ∧ p ≠ b ∧ Rectangle a b p := by
  refine ⟨(a.1, time), Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨hkey, rfl⟩),
    ?_, ?_, ?_⟩
  · intro h; have := congrArg (fun p : Point => p.2) h; simp only at this; omega
  · intro h
    have heq := congrArg (fun p : Point => p.1) h
    exact hx heq
  · exact ⟨min_le_left _ _, le_max_left _ _, by omega, by omega⟩

private theorem sweep_cross {n time request : Nat} {P : Finset Point}
    (hist : History n time P) {a b : Point} (ha : a ∈ P)
    (hb : b ∈ row time (greedySweep time request P)) (hx : a.1 ≠ b.1) :
    ∃ p ∈ P ∪ row time (greedySweep time request P),
      p ≠ a ∧ p ≠ b ∧ Rectangle a b p := by
  obtain ⟨hbkey, hbtime⟩ := (mem_row b time _).mp hb
  have hat := (hist a ha).2
  by_cases hakey : a.1 ∈ greedySweep time request P
  · exact projection hat hbtime hx hakey
  have hareq : a.1 ≠ request := by intro h; apply hakey; simp [greedySweep, h]
  have notvisible : ¬ Visible P time request a := by
    intro h
    exact hakey (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨a, Finset.mem_filter.mpr ⟨ha, h⟩, rfl⟩))
  have witness : ∃ p ∈ P, p ≠ a ∧ Rectangle a (request, time) p := by
    have hn : ¬ (∀ p ∈ P, p ≠ a → ¬ Rectangle a (request, time) p) :=
      fun h => notvisible ⟨hareq, h⟩
    push Not at hn
    exact hn
  obtain ⟨p, hp, hpa, hpr⟩ := witness
  have hpt := (hist p hp).2
  have hpb : p ≠ b := by intro h; have := congrArg Prod.snd h; omega
  have oldWitness (hr : Rectangle a b p) :
      ∃ p ∈ P ∪ row time (greedySweep time request P),
        p ≠ a ∧ p ≠ b ∧ Rectangle a b p :=
    ⟨p, Finset.mem_union_left _ hp, hpa, hpb, hr⟩
  rcases Finset.mem_insert.mp hbkey with hbr | hbkey
  · apply oldWitness
    have beq : b = (request, time) := Prod.ext hbr hbtime
    simpa only [beq] using hpr
  obtain ⟨q, hq, hqb⟩ := Finset.mem_image.mp hbkey
  obtain ⟨hq, hqvis⟩ := Finset.mem_filter.mp hq
  have hqt := (hist q hq).2
  by_cases hqa : a.2 ≤ q.2
  · refine ⟨q, Finset.mem_union_left _ hq, ?_, ?_, ?_⟩
    · intro h; have := congrArg Prod.fst h; omega
    · intro h; have := congrArg Prod.snd h; omega
    · unfold Rectangle
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega
  by_cases reqrect : Rectangle a b (request, time)
  · refine ⟨(request, time), Finset.mem_union_right _ ?_, ?_, ?_, reqrect⟩
    · apply (mem_row _ _ _).mpr
      simp [greedySweep]
    · intro h; have := congrArg (fun p : Point => p.1) h; exact hareq this.symm
    · intro h; have := congrArg (fun p : Point => p.1) h; exact hqvis.1 (hqb.trans this.symm)
  apply oldWitness
  have hpq : p ≠ q := by intro h; subst p; unfold Rectangle at hpr; omega
  have outside := hqvis.2 p hp hpq
  unfold Rectangle at hpr reqrect outside ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hpr
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

theorem sweep_correct {n time request : Nat} {P : Finset Point}
    (hist : History n time P) (sat : ASS P) (valid : request < n) :
    Completion n time request P (greedySweep time request P) := by
  refine ⟨by simp [greedySweep], ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_range.mpr valid
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hist q (Finset.mem_filter.mp hq).1).1
  · intro a ha b hb hx hy
    rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨p, hp, hpa, hpb, hr⟩ := sat a ha b hb hx hy
      exact ⟨p, Finset.mem_union_left _ hp, hpa, hpb, hr⟩
    · exact sweep_cross hist ha hb hx
    · obtain ⟨p, hp, hpb, hpa, hr⟩ := sweep_cross hist hb ha (Ne.symm hx)
      exact ⟨p, hp, hpa, hpb, (rectangle_symm b a p).mp hr⟩
    · exact (hy (((mem_row a time _).mp ha).2.trans
        ((mem_row b time _).mp hb).2.symm)).elim

theorem sweep_greedy {n time request : Nat} {P : Finset Point}
    (hist : History n time P) (sat : ASS P) (valid : request < n) :
    GreedyRow n time request P (greedySweep time request P) :=
  ⟨sweep_correct hist sat valid, fun _ h => Finset.card_le_card (sweep_subset hist h)⟩

theorem greedy_unique {n time request : Nat} {P : Finset Point} {keys : Finset Nat}
    (hist : History n time P) (sat : ASS P) (valid : request < n)
    (greedyKeys : GreedyRow n time request P keys) :
    keys = greedySweep time request P := by
  exact (Finset.eq_of_subset_of_card_le (sweep_subset hist greedyKeys.1)
    (greedyKeys.2 _ (sweep_correct hist sat valid))).symm

end RotationBST.Arboral
