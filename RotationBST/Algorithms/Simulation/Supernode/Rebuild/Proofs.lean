module

public import RotationBST.Algorithms.Simulation.Supernode.Rebuild.Defs
public import RotationBST.Algorithms.Simulation.Supernode.Assembly.Decomposition
public import RotationBST.Algorithms.Simulation.Supernode.Nested.Promotion
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Initialize.Proofs

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode
open Split.Multiway.Finger.TwoEnded

/-- Rebuilding a nonempty exposed region creates the next canonical root
supernode. Its rotation cost and entire future split budget are charged only
to the exposed keys; attached subtree sizes do not enter the bound. -/
theorem Assembly.rebuild_nonempty {n time : Nat} {P : Finset Point}
    (history : History n time P) {assembly : Assembly} {lo : Nat}
    (valid : assembly.Valid P lo) (nonempty : 0 < assembly.shape.size) :
    Represents (P ∪ row time (Region.keys assembly.region lo)) lo assembly.rebuild ∧
      ∃ cost, Rotations assembly.region.tree assembly.rebuild.tree cost ∧
        cost + intervalCredit (initialInterval assembly.shape.size) ≤
          6016 * (Region.keys assembly.region lo).card := by
  have initialized := initialInterval_valid assembly.shape.size
  have sizes := initialInterval_size assembly.shape.size
  obtain ⟨cost, steps, budget⟩ := initialInterval_budget assembly.shape
  cases choice : initialInterval assembly.shape.size with
  | none => rw [choice] at sizes; simp only [intervalTree, Tree.size] at sizes; omega
  | some state =>
    rw [choice] at initialized sizes steps budget
    have stateSize : state.size = assembly.shape.size := by
      simpa only [intervalTree, state_size] using sizes
    have arity : assembly.children.length = state.size + 1 := by rw [assembly.children_length, stateSize]
    let gaps := fun (j : Nat) => ((assembly.children.map Nested.tree)[j]?).getD Tree.nil
    have same := withGaps_same steps gaps 0 lo
    have source : withGaps assembly.shape gaps 0 = assembly.region := assembly.decomposition
    rw [source] at same
    have promoted := Represents.promote history lo state assembly.children initialized arity
      (fun i => valid.children i)
    have keys : Region.keys assembly.region lo = Region.keys (nestedRegion state assembly.children) lo := same.2.1
    constructor
    · rw [Assembly.rebuild, choice]
      rw [keys]
      exact promoted
    · refine ⟨cost, ?_, ?_⟩
      · have lifted := (withGaps_rotations steps gaps 0).1
        rw [source] at lifted
        simpa only [Assembly.rebuild, choice, Nested.tree, intervalTree] using lifted
      · rw [Region.keys_card, ← assembly.shape_size]
        exact budget

/-- Complete rebuilding specification, including the unchanged singleton-hole
case when the row exposes no key in this interval. -/
theorem Assembly.rebuild_spec {n time : Nat} {P : Finset Point}
    (history : History n time P) {assembly : Assembly} {lo : Nat}
    (valid : assembly.Valid P lo) :
    Represents (P ∪ row time (Region.keys assembly.region lo)) lo assembly.rebuild ∧
      ∃ cost, Rotations assembly.region.tree assembly.rebuild.tree cost ∧
        cost + intervalCredit (initialInterval assembly.shape.size) ≤
          6016 * (Region.keys assembly.region lo).card := by
  cases assembly with
  | hole state =>
    simp only [Assembly.region, Region.keys, Assembly.rebuild, Assembly.shape, Tree.size,
      initialInterval, Assembly.children, List.getElem?_cons_zero, Option.getD_some]
    constructor
    · change Represents P lo state at valid
      simpa only [row, Finset.image_empty, Finset.union_empty] using valid
    · exact ⟨0, .refl, by simp [intervalCredit, intervalNodes, intervalTree, Tree.size]⟩
  | node left right =>
    exact Assembly.rebuild_nonempty history valid (by simp only [Assembly.shape, Tree.size]; omega)

end RotationBST.Geometric.Online.Supernode
