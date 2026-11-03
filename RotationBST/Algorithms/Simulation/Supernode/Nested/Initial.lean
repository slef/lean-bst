module

public import RotationBST.Algorithms.Simulation.Supernode.Nested.Proofs
public import RotationBST.Algorithms.Simulation.Supernode.Ranks.Proofs
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Initialize.Proofs
public import RotationBST.Models.Region.View.Defs

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode
open Split.Multiway.Finger.TwoEnded

private theorem empty_children (count : Nat) :
    (fun (i : Nat) => (((List.replicate count Nested.empty).map Nested.tree)[i]?).getD .nil) =
      (fun _ => Tree.nil) := by
  funext i
  by_cases inside : i < count <;> simp [Nested.tree, inside]

private theorem empty_weight (offset count : Nat) : gapWeight (fun _ => Tree.nil) offset count = 0 := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih => simp [gapWeight, Tree.size, ih]

private theorem empty_region_keys (shape : Tree) (lo : Nat) :
    Region.keys (withGaps shape (fun _ => .nil) 0) lo = Finset.Ico lo (lo + shape.size) := by
  ext key
  rw [withGaps_keys]
  simp only [keyRank, empty_weight, Nat.add_zero, Finset.mem_Ico]
  constructor
  · rintro ⟨rank, bound, rfl⟩; omega
  · rintro ⟨lower, upper⟩
    exact ⟨key - lo, by omega, by omega⟩

private theorem empty_region_size (shape : Tree) :
    (withGaps shape (fun _ => .nil) 0).tree.size = shape.size := by
  rw [withGaps_tree_size, empty_weight, Nat.add_zero]

private theorem initial_layer (state : State) (balanced : state.HeightValid) (lo : Nat) :
    Represents ∅ lo (.layer state (List.replicate (state.size + 1) .empty)) := by
  apply Represents.layer lo state _ balanced (by simp)
  · simp only [nestedRegion, empty_children, empty_region_keys, empty_region_size]
    have emptyPriority : lastTouch ∅ = fun _ => (⊥ : WithBot Nat) := by
      funext key
      simp [lastTouch]
    simp [supernodeKeys, supernodePriority, emptyPriority]
  · intro i
    simpa using Represents.empty (P := ∅)
      (lo + i.val + gapWeight
        (fun j => (((List.replicate (state.size + 1) Nested.empty).map Nested.tree)[j]?).getD .nil) 0 i.val)

theorem initialNested_represents (n : Nat) : Represents ∅ 0 (initialNested n) := by
  have valid := initialInterval_valid n
  cases initial : initialInterval n with
  | none => simpa only [initialNested, initial] using Represents.empty (P := ∅) 0
  | some state =>
    rw [initial] at valid
    simpa only [initialNested, initial] using initial_layer state valid 0

theorem initialNested_size (n : Nat) : (initialNested n).tree.size = n := by
  have sizes := initialInterval_size n
  cases initial : initialInterval n with
  | none => simpa only [initialNested, initial, Nested.tree, intervalTree] using sizes
  | some state =>
    rw [initial] at sizes
    simpa only [initialNested, initial, Nested.tree, empty_children, empty_region_size, intervalTree] using sizes

end RotationBST.Geometric.Online.Supernode
