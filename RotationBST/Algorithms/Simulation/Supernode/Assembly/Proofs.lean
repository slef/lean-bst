module

public import RotationBST.Algorithms.Simulation.Supernode.Assembly.Defs
public import RotationBST.Algorithms.Simulation.Supernode.Nested.Retention

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode
open Split.Multiway.Finger.TwoEnded

/-- Materializing retained intervals does not change the full embedded BST. -/
theorem assemblePartition_tree (parts : Partitioned) (children : List Nested) (first : Nat)
    (fits : first + parts.tree.size + 1 ≤ children.length) :
    (assemblePartition parts children first).region.tree =
      (withGaps parts.tree (fun j => ((children.map Nested.tree)[j]?).getD .nil) first).tree := by
  induction parts generalizing first with
  | leaf interval =>
    cases interval with
    | none =>
      have inside : first < children.length := by
        simp only [Partitioned.tree, intervalTree, Tree.size] at fits
        omega
      simp only [assemblePartition, Assembly.region, Partitioned.tree, intervalTree, withGaps,
        Pointer.Lazy.Skeleton.tree, List.getElem?_map, List.getElem?_eq_getElem inside,
        Option.map_some, Option.getD_some]
    | some state =>
      exact retainedNested_tree state children first (by simpa only [Partitioned.tree, intervalTree, state_size] using fits)
  | branch left right il ir =>
    simp only [Partitioned.tree, Tree.size] at fits
    simp only [assemblePartition, Assembly.region, Pointer.Lazy.Skeleton.tree, Partitioned.tree, withGaps]
    rw [il first (by omega), ir (first + left.tree.size + 1) (by omega)]

/-- Every hole of a materialized split hierarchy is recursively represented at
its correct full-tree offset. This includes empty parent intervals. -/
theorem assemblePartition_valid {P : Finset Point} {lo : Nat} {state : State} {children : List Nested}
    (represented : Represents P lo (.layer state children)) (parts : Partitioned)
    (valid : parts.Valid) (first : Nat) (fits : first + parts.tree.size ≤ state.size) :
    (assemblePartition parts children first).Valid P
      (lo + first + gapWeight (fun j => ((children.map Nested.tree)[j]?).getD .nil) 0 first) := by
  have arity : children.length = state.size + 1 := by cases represented; assumption
  induction parts generalizing first with
  | leaf interval =>
    cases interval with
    | none =>
      have inside : first < children.length := by
        simp only [Partitioned.tree, intervalTree, Tree.size] at fits
        omega
      simp only [assemblePartition, Assembly.Valid, List.getElem?_eq_getElem inside, Option.getD_some]
      cases represented with
      | layer _ _ _ _ _ _ subtrees => exact subtrees ⟨first, inside⟩
    | some replacement =>
      exact represented.retain replacement valid first
        (by simpa only [Partitioned.tree, intervalTree, state_size] using fits)
  | branch left right il ir =>
    simp only [Partitioned.tree, Tree.size] at fits
    refine ⟨il valid.1 first (by omega), ?_⟩
    have child := ir valid.2 (first + left.tree.size + 1) (by omega)
    have tree := assemblePartition_tree left children first (by omega)
    have weights := gapWeight_add (fun j => ((children.map Nested.tree)[j]?).getD Tree.nil) 0 first (left.tree.size + 1)
    simp only [Nat.zero_add, ← Nat.add_assoc] at weights
    change (assemblePartition right children (first + left.tree.size + 1)).Valid P _
    rw [tree, withGaps_tree_size]
    convert child using 1; omega

end RotationBST.Arboral.Online.Supernode
