module

public import RotationBST.Algorithms.Simulation.Supernode.Assembly.Selection

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode
open Split.Multiway.Finger.TwoEnded

/-- Materialization exposes exactly the separator ranks, expanded through the
original gap sizes to their absolute full-BST positions. -/
theorem assemblePartition_keys (parts : Partitioned) (children : List Nested) (lo first key : Nat)
    (fits : first + parts.tree.size + 1 ≤ children.length) :
    key ∈ Region.keys (assemblePartition parts children first).region
        (lo + first + gapWeight (fun j => ((children.map Nested.tree)[j]?).getD .nil) 0 first) ↔
      ∃ rank ∈ parts.keys first,
        key = lo + keyRank (fun j => ((children.map Nested.tree)[j]?).getD .nil) 0 rank := by
  induction parts generalizing first with
  | leaf interval => cases interval <;> simp [assemblePartition, Assembly.region, Region.keys, Partitioned.keys]
  | branch left right il ir =>
    let gaps := fun (j : Nat) => ((children.map Nested.tree)[j]?).getD Tree.nil
    have fitLeft : first + left.tree.size + 1 ≤ children.length := by
      simp only [Partitioned.tree, Tree.size] at fits
      omega
    have fitRight : first + left.tree.size + 1 + right.tree.size + 1 ≤ children.length := by
      simp only [Partitioned.tree, Tree.size] at fits
      omega
    have tree := assemblePartition_tree left children first fitLeft
    have root : lo + first + gapWeight gaps 0 first +
        (assemblePartition left children first).region.tree.size =
        lo + keyRank gaps 0 (first + left.tree.size) := by
      rw [tree]
      simpa only [Nat.zero_add] using segment_end left.tree gaps 0 lo first
    have next : lo + first + gapWeight gaps 0 first +
        (assemblePartition left children first).region.tree.size + 1 =
        lo + (first + left.tree.size + 1) + gapWeight gaps 0 (first + left.tree.size + 1) := by
      rw [root]
      simp only [keyRank]
      omega
    simp only [assemblePartition, Assembly.region, Region.keys, Finset.mem_insert, Finset.mem_union]
    change (key = lo + first + gapWeight gaps 0 first + _ ∨ _ ∨ _) ↔ _
    rw [next, root, il first fitLeft, ir (first + left.tree.size + 1) fitRight]
    simp only [Partitioned.keys, List.mem_append, List.mem_cons]
    constructor
    · rintro (equal | ⟨rank, member, equal⟩ | ⟨rank, member, equal⟩)
      · exact ⟨first + left.tree.size, Or.inr (Or.inl rfl), equal⟩
      · exact ⟨rank, Or.inl member, equal⟩
      · exact ⟨rank, Or.inr (Or.inr member), equal⟩
    · rintro ⟨rank, member, equal⟩
      rcases member with member | same | member
      · exact Or.inr (Or.inl ⟨rank, member, equal⟩)
      · subst rank
        exact Or.inl equal
      · exact Or.inr (Or.inr ⟨rank, member, equal⟩)

/-- The executable parent stage exposes precisely the intersection of this
row with the old parent supernode; child-gap touches are excluded. -/
theorem selectParent_keys {P : Finset Point} {lo : Nat} {state : State} {children : List Nested}
    (represented : Represents P lo (.layer state children)) (keys : Finset Nat) :
    Region.keys (selectParent state children lo keys).1.region lo =
      keys ∩ Region.keys (nestedRegion state children) lo := by
  have balanced : state.HeightValid := by cases represented; assumption
  have arity : children.length = state.size + 1 := by cases represented; assumption
  let gaps := fun (j : Nat) => ((children.map Nested.tree)[j]?).getD Tree.nil
  let ranks := touchedRanks state.tree.size gaps 0 lo keys
  have bounds : ∀ key ∈ ranks, key < (intervalTree (some state)).size := by
    intro key member
    exact Finset.mem_range.mp (Finset.mem_filter.mp member).1
  have spec := selectKeys_spec (some state) ranks balanced bounds
  have size := spec.2.1.size_eq
  have fits : (selectKeys (some state) ranks).1.tree.size = state.size := by
    simpa only [intervalTree, state_size] using size.symm
  have images := touchedRanks_image state.tree gaps 0 lo keys
  simp only [nestedRegion]
  rw [← images]
  ext key
  have expanded := assemblePartition_keys (selectKeys (some state) ranks).1 children lo 0 key (by omega)
  simp only [Nat.add_zero, gapWeight, spec.2.2.1] at expanded
  change key ∈ Region.keys (assemblePartition (selectKeys (some state) ranks).1 children 0).region lo ↔ _
  rw [expanded]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨rank, member, equal⟩
    exact ⟨rank, (Finset.mem_sort (· ≤ ·)).mp member, equal.symm⟩
  · rintro ⟨rank, member, equal⟩
    exact ⟨rank, (Finset.mem_sort (· ≤ ·)).mpr member, equal.symm⟩

end RotationBST.Geometric.Online.Supernode
