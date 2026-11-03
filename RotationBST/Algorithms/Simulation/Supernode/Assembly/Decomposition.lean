module

public import RotationBST.Algorithms.Simulation.Supernode.Assembly.Attachment

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode

theorem Assembly.children_length (assembly : Assembly) :
    assembly.children.length = assembly.shape.size + 1 := by
  induction assembly with
  | hole state => rfl
  | node left right il ir => simp only [children, shape, List.length_append, Tree.size, il, ir]; omega

theorem Assembly.shape_size (assembly : Assembly) : assembly.shape.size = assembly.region.size := by
  induction assembly with
  | hole state => rfl
  | node left right il ir => simp only [shape, region, Tree.size, Pointer.Lazy.Skeleton.size, il, ir]

/-- Every assembled region is exactly its key-only shape with its ordered
nested children inserted into the external gaps. -/
theorem Assembly.decomposition (assembly : Assembly) :
    withGaps assembly.shape (fun i => ((assembly.children.map Nested.tree)[i]?).getD .nil) 0 =
      assembly.region := by
  induction assembly with
  | hole state => simp [shape, children, region, withGaps]
  | node left right il ir =>
    simp only [shape, children, withGaps, region]
    congr 1
    · rw [← il]
      apply withGaps_congr
      intro i bound
      have inside : i < (left.children.map Nested.tree).length := by
        rw [List.length_map, children_length]
        omega
      simp only [List.map_append, Nat.zero_add, List.getElem?_append_left inside]
    · rw [← ir]
      apply withGaps_congr
      intro i _
      have length : (left.children.map Nested.tree).length = left.shape.size + 1 := by
        rw [List.length_map, children_length]
      simp only [List.map_append, Nat.zero_add]
      rw [List.getElem?_append_right (by rw [length]; omega), length]
      congr 2
      omega

/-- The ordered children retain their recursive invariants at the offsets
obtained by summing the sizes of preceding gaps and exposed keys. -/
theorem Assembly.Valid.children {P : Finset Point} {assembly : Assembly} {lo : Nat}
    (valid : assembly.Valid P lo) (i : Fin assembly.children.length) :
    Represents P
      (lo + i.val + gapWeight (fun j => ((assembly.children.map Nested.tree)[j]?).getD .nil) 0 i.val)
      assembly.children[i] := by
  induction assembly generalizing lo with
  | hole state =>
    have zero : i.val = 0 := by have h := i.isLt; simp only [Assembly.children, List.length_singleton] at h; omega
    change Represents P (lo + i.val + gapWeight _ 0 i.val) ([state][i.val])
    simp only [zero, gapWeight, Nat.add_zero, List.getElem_cons_zero]
    exact valid
  | node left right il ir =>
    let gaps := fun (j : Nat) => (((left.children ++ right.children).map Nested.tree)[j]?).getD Tree.nil
    let lg := fun (j : Nat) => ((left.children.map Nested.tree)[j]?).getD Tree.nil
    let rg := fun (j : Nat) => ((right.children.map Nested.tree)[j]?).getD Tree.nil
    have leftSame (j : Nat) (bound : j < left.children.length) : gaps j = lg j := by
      simp only [gaps, lg, List.map_append]
      rw [List.getElem?_append_left (by simpa only [List.length_map] using bound)]
    have rightSame (j : Nat) : gaps (left.children.length + j) = rg j := by
      simp only [gaps, rg, List.map_append]
      rw [List.getElem?_append_right (by rw [List.length_map]; omega), List.length_map]
      simp only [Nat.add_sub_cancel_left]
    by_cases inLeft : i.val < left.children.length
    · have child := il valid.1 ⟨i.val, inLeft⟩
      have weight : gapWeight gaps 0 i.val = gapWeight lg 0 i.val := by
        apply gapWeight_congr
        intro j bound
        simpa only [Nat.zero_add] using leftSame j (by omega)
      change Represents P (lo + i.val + gapWeight gaps 0 i.val) (left.children ++ right.children)[i.val]
      rw [List.getElem_append_left inLeft, weight]
      exact child
    · have bound : i.val - left.children.length < right.children.length := by
        have h := i.isLt
        simp only [Assembly.children, List.length_append] at h
        omega
      have child := ir valid.2 ⟨i.val - left.children.length, bound⟩
      have prefixWeight : gapWeight gaps 0 left.children.length = gapWeight lg 0 left.children.length := by
        apply gapWeight_congr
        intro j below
        simpa only [Nat.zero_add] using leftSame j below
      have suffixWeight : gapWeight gaps left.children.length (i.val - left.children.length) =
          gapWeight rg 0 (i.val - left.children.length) := by
        apply gapWeight_congr
        intro j _
        simpa only [Nat.zero_add] using rightSame j
      have total := gapWeight_add gaps 0 left.children.length (i.val - left.children.length)
      rw [show left.children.length + (i.val - left.children.length) = i.val by omega,
        Nat.zero_add, prefixWeight, suffixWeight] at total
      have size : left.region.tree.size = left.shape.size + gapWeight lg 0 left.children.length := by
        rw [← left.decomposition, withGaps_tree_size, left.children_length]
      have length := left.children_length
      change Represents P (lo + i.val + gapWeight gaps 0 i.val) (left.children ++ right.children)[i.val]
      rw [List.getElem_append_right (by omega)]
      dsimp only at child
      dsimp only [rg] at total
      convert child using 1; omega

end RotationBST.Geometric.Online.Supernode
