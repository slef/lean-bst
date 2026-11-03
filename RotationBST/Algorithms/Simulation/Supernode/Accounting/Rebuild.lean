module

public import RotationBST.Algorithms.Simulation.Supernode.Accounting.Defs
public import RotationBST.Algorithms.Simulation.Supernode.Rebuild.Proofs

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode
open SplitTree.Multiway.Finger.TwoEnded

theorem Assembly.children_credit (assembly : Assembly) :
    (assembly.children.map Nested.credit).sum = assembly.credit := by
  induction assembly with
  | hole state => simp [Assembly.children, Assembly.credit]
  | node left right il ir =>
    simp only [Assembly.children, List.map_append, List.sum_append, Assembly.credit, il, ir]

/-- Rebuilding allocates credit only for the new outer supernode. All stored
child credits pass unchanged into the next nested state. -/
theorem Assembly.rebuild_credit (assembly : Assembly) :
    assembly.rebuild.credit = intervalCredit (initialInterval assembly.shape.size) + assembly.credit := by
  cases choice : initialInterval assembly.shape.size with
  | some state =>
    simp only [Assembly.rebuild, choice, Nested.credit, assembly.children_credit]
  | none =>
    have size := initialInterval_size assembly.shape.size
    rw [choice] at size
    simp only [intervalTree, Tree.size] at size
    cases assembly with
    | hole state =>
      simp [Assembly.rebuild, Assembly.shape, Tree.size, initialInterval, Assembly.children,
        Assembly.credit, intervalCredit, intervalNodes, intervalTree]
    | node left right => simp only [Assembly.shape, Tree.size] at size; omega

/-- Rebuilding adds at most a constant amount of total nested potential per
new row key, including the rotations that create the new outer supernode. -/
theorem Assembly.rebuild_budget {n time : Nat} {P : Finset Point}
    (history : History n time P) {assembly : Assembly} {lo : Nat}
    (valid : assembly.Valid P lo) :
    ∃ cost, Rotations assembly.region.tree assembly.rebuild.tree cost ∧
      cost + assembly.rebuild.credit ≤ assembly.credit + 6016 * (Region.keys assembly.region lo).card := by
  obtain ⟨cost, steps, bound⟩ := (Assembly.rebuild_spec history valid).2
  refine ⟨cost, steps, ?_⟩
  rw [assembly.rebuild_credit]
  omega

end RotationBST.Geometric.Online.Supernode
