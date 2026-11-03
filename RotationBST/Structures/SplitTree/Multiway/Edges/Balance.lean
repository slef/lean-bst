module

public import RotationBST.Structures.SplitTree.Multiway.Edges.Proofs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway

/-- Repairs inside larger parents preserve height; only a minimal root can shrink. -/
theorem Balanced.repairFirst {h : Nat} {t : Multiway} (valid : Balanced h t) :
    Balanced h (t.repairFirst).1 ∨ ∃ k, h = k + 1 ∧ Balanced k (t.repairFirst).1 := by
  cases valid with
  | nil => exact Or.inl .nil
  | two ha hb => exact (Balanced.two ha hb).prepareLeft
  | three ha hb hc =>
    apply Or.inl
    cases ha <;> cases hb <;> simp only [Multiway.repairFirst, Multiway.prepareLeft]
    all_goals solve_by_elim (maxDepth := 20) [Balanced.nil, Balanced.two, Balanced.three, Balanced.four]
  | four ha hb hc hd =>
    apply Or.inl
    cases ha <;> cases hb <;> simp only [Multiway.repairFirst, Multiway.prepareLeft]
    all_goals solve_by_elim (maxDepth := 20) [Balanced.nil, Balanced.two, Balanced.three, Balanced.four]

theorem Balanced.repairLast {h : Nat} {t : Multiway} (valid : Balanced h t) :
    Balanced h (t.repairLast).1 ∨ ∃ k, h = k + 1 ∧ Balanced k (t.repairLast).1 := by
  cases valid with
  | nil => exact Or.inl .nil
  | two ha hb => exact (Balanced.two ha hb).prepareRight
  | three ha hb hc =>
    apply Or.inl
    cases hb <;> cases hc <;> simp only [Multiway.repairLast, Multiway.prepareRight]
    all_goals solve_by_elim (maxDepth := 20) [Balanced.nil, Balanced.two, Balanced.three, Balanced.four]
  | four ha hb hc hd =>
    apply Or.inl
    cases hc <;> cases hd <;> simp only [Multiway.repairLast, Multiway.prepareRight]
    all_goals solve_by_elim (maxDepth := 20) [Balanced.nil, Balanced.two, Balanced.three, Balanced.four]

end RotationBST.Geometric.Split.Multiway
