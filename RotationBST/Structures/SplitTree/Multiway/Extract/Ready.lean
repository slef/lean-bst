module

public import RotationBST.Structures.SplitTree.Multiway.Extract.Rotations

@[expose] public section
namespace RotationBST.SplitTree.Multiway

/-- With root contraction excluded, repair makes the first child safe to enter.
A previously wide parent either stays wide or has a nonempty repaired child. -/
theorem repairFirst_ready {h : Nat} {t : Multiway} (valid : Balanced h t)
    (noMerge : t.rootMerge = none) :
    Balanced h (t.repairFirst).1 ∧
      (firstChild (t.repairFirst).1 = .nil ∨ Wide (firstChild (t.repairFirst).1)) ∧
      (Wide t → Wide (t.repairFirst).1 ∨ firstChild (t.repairFirst).1 ≠ .nil) := by
  cases valid with
  | nil => exact ⟨.nil, Or.inl rfl, False.elim⟩
  | two ha hb =>
    cases ha <;> cases hb <;>
      simp [rootMerge, repairFirst, prepareLeft, firstChild, Wide] at noMerge ⊢
    all_goals solve_by_elim (maxDepth := 30) [Balanced.nil, Balanced.two, Balanced.three, Balanced.four]
  | three ha hb hc =>
    cases ha <;> cases hb <;>
      simp [rootMerge, repairFirst, prepareLeft, firstChild, Wide] at noMerge ⊢
    all_goals solve_by_elim (maxDepth := 30) [Balanced.nil, Balanced.two, Balanced.three, Balanced.four]
  | four ha hb hc hd =>
    cases ha <;> cases hb <;>
      simp [rootMerge, repairFirst, prepareLeft, firstChild, Wide] at noMerge ⊢
    all_goals solve_by_elim (maxDepth := 30) [Balanced.nil, Balanced.two, Balanced.three, Balanced.four]

/-- A root contraction lowers the height and leaves a wide root. -/
theorem rootMerge_balance {h : Nat} {t u : Multiway} (valid : Balanced h t)
    (merged : t.rootMerge = some u) : ∃ k, h = k + 1 ∧ Balanced k u ∧ Wide u := by
  cases valid with
  | nil => simp [rootMerge] at merged
  | three ha hb hc => simp [rootMerge] at merged
  | four ha hb hc hd => simp [rootMerge] at merged
  | two hl hr =>
    cases hl with
    | nil => simp [rootMerge] at merged
    | three ha hb hc => simp [rootMerge] at merged
    | four ha hb hc hd => simp [rootMerge] at merged
    | two ha hb =>
      cases hr with
      | three hc hd he => simp [rootMerge] at merged
      | four hc hd he hf => simp [rootMerge] at merged
      | two hc hd =>
        simp only [rootMerge, Option.some.injEq] at merged
        subst u
        exact ⟨_, rfl, .four ha hb hc hd, trivial⟩

end RotationBST.SplitTree.Multiway
