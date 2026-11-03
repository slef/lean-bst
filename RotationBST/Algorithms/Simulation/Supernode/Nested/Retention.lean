module

public import RotationBST.Algorithms.Simulation.Supernode.Nested.Locality
public import RotationBST.Algorithms.Simulation.Supernode.Ranks.Restriction
public import RotationBST.Algorithms.Simulation.Supernode.Embedding.Congruence

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode
open SplitTree.Multiway.Finger.TwoEnded

/-- Splitting a parent keeps a consecutive child list with exactly one more
child than surviving parent keys. -/
theorem retained_children_length (state : State) (children : List Nested) (first : Nat)
    (fits : first + state.size + 1 ≤ children.length) :
    ((children.drop first).take (state.size + 1)).length = state.size + 1 := by
  simp only [List.length_take, List.length_drop]
  omega

/-- Retention preserves the full embedded subtree, including every gap. -/
theorem retainedNested_tree (state : State) (children : List Nested) (first : Nat)
    (fits : first + state.size + 1 ≤ children.length) :
    (retainedNested state children first).tree =
      (withGaps state.tree (fun j => ((children.map Nested.tree)[j]?).getD .nil) first).tree := by
  simp only [retainedNested, Nested.tree]
  apply congrArg Pointer.Lazy.Skeleton.tree
  apply withGaps_congr
  intro i bound
  have inside : i < ((children.drop first).take (state.size + 1)).length := by
    rw [retained_children_length state children first fits]
    rw [state_size] at bound
    omega
  have original : first + i < children.length := by rw [state_size] at bound; omega
  simp only [Nat.zero_add, List.getElem?_map, List.getElem?_eq_getElem inside,
    List.getElem?_eq_getElem original, Option.map_some, Option.getD_some,
    List.getElem_take, List.getElem_drop]

/-- A retained interval is a valid nested state, including all recursively
represented children. Only the parent key shape changes. -/
theorem Represents.retain {P : Finset Point} {lo : Nat} {state : State} {children : List Nested}
    (valid : Represents P lo (.layer state children))
    (replacement : State) (balanced : replacement.HeightValid) (first : Nat)
    (fits : first + replacement.size ≤ state.size) :
    Represents P
      (lo + first + gapWeight (fun j => ((children.map Nested.tree)[j]?).getD .nil) 0 first)
      (retainedNested replacement children first) := by
  cases valid with
  | layer _ _ _ _ arity canonical subtrees =>
    let kept := (children.drop first).take (replacement.size + 1)
    let gaps := fun (j : Nat) => ((children.map Nested.tree)[j]?).getD Tree.nil
    let keptGaps := fun (j : Nat) => ((kept.map Nested.tree)[j]?).getD Tree.nil
    let start := lo + first + gapWeight gaps 0 first
    have length : kept.length = replacement.size + 1 :=
      retained_children_length replacement children first (by omega)
    have lookup (i : Nat) (bound : i < kept.length) :
        kept[i] = children[first + i]'(by omega) := by
      simp only [kept, List.getElem_take, List.getElem_drop]
    have gapSame (i : Nat) (bound : i ≤ replacement.size) : keptGaps i = gaps (first + i) := by
      have inside : i < kept.length := by omega
      have original : first + i < children.length := by omega
      simp only [keptGaps, gaps, List.getElem?_map,
        List.getElem?_eq_getElem inside, List.getElem?_eq_getElem original,
        Option.map_some, Option.getD_some, lookup i inside]
    have region : nestedRegion replacement kept = withGaps replacement.tree gaps first := by
      apply withGaps_congr
      intro i bound
      simpa only [Nat.zero_add] using gapSame i (by rwa [state_size] at bound)
    change Represents P start (.layer replacement kept)
    refine .layer start replacement kept balanced length ?_ ?_
    · rw [region]
      have positive : 0 < replacement.tree.size := by
        rw [state_size]
        simp only [State.size]
        omega
      simpa only [Nat.zero_add] using withGaps_segment_canonical state.tree replacement.tree gaps 0 lo first canonical
        (by simpa only [state_size] using fits) positive
    · intro i
      have oldBound : first + i.val < children.length := by have h := i.isLt; omega
      have child := subtrees ⟨first + i.val, oldBound⟩
      have sameWeight : gapWeight keptGaps 0 i.val = gapWeight gaps first i.val := by
        apply gapWeight_congr
        intro j bound
        simpa only [Nat.zero_add] using gapSame j (by have h := i.isLt; omega)
      have weights := gapWeight_add gaps 0 first i.val
      simp only [Nat.zero_add] at weights
      have equalStart : start + i.val + gapWeight keptGaps 0 i.val =
          lo + (first + i.val) + gapWeight gaps 0 (first + i.val) := by
        dsimp only [start]
        omega
      change Represents P (start + i.val + gapWeight keptGaps 0 i.val) kept[i.val]
      rw [equalStart, lookup i.val i.isLt]
      exact child

end RotationBST.Geometric.Online.Supernode
