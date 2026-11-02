module

public import RotationBST.Tango.State.Nesting.Edits.Cut
public import RotationBST.Tango.State.Nesting.Edits.Join

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Realize a reference-component interval cut in any equivalent auxiliary
shape. Both the resulting nesting and the full-state cost are specified. -/
theorem cutInterval_simulates (s reference : MarkedTree) (same : s.nesting = reference.nesting)
    (i j : Nat) (ordered : i < j) (valid : j ≤ reference.region.size)
    (proper : j - i < reference.region.size) :
    (s.cutInterval i j).1.nesting = reference.nesting.group i (j - i + 1) ∧
      Rotations s.tree (s.cutInterval i j).1.tree (s.cutInterval i j).2 ∧
      ((s.cutInterval i j).2 : ℝ) + (s.cutInterval i j).1.potential - s.potential ≤
        6 * Real.logb 2 reference.region.size + 2 := by
  have sizes := nesting_region_size_eq same
  simpa only [same, sizes] using cutInterval_spec s i j ordered (by omega) (by omega)

/-- Realize a merge selected by a slot in the reference fringe. The matched
actual component may have a different auxiliary binary shape. -/
theorem mergeAt_simulates (s reference child : MarkedTree) (same : s.nesting = reference.nesting)
    (i : Nat) (positive : 0 < reference.region.size) (valid : i ≤ reference.region.size)
    (attached : reference.fringe[i]? = some child) :
    (s.mergeAt i).1.nesting = reference.nesting.merge i ∧
      Rotations s.tree (s.mergeAt i).1.tree (s.mergeAt i).2 ∧
      ((s.mergeAt i).2 : ℝ) + (s.mergeAt i).1.potential - s.potential ≤
        8 * Real.logb 2 (reference.region.size + child.region.size : Nat) + 2 := by
  have sizes := nesting_region_size_eq same
  have hs : i < s.fringe.length := by rw [marked_fringe_length]; omega
  have hr : i < reference.fringe.length := by rw [marked_fringe_length]; omega
  let actual := s.fringe[i]'hs
  have matching := (nesting_fringe_matching same).get hs hr
  have refkey : reference.fringe[i]'hr = child := by
    rw [List.getElem?_eq_getElem hr] at attached
    exact Option.some.inj attached
  have nested : actual.nesting = child.nesting := by simpa only [List.get_eq_getElem, refkey] using matching
  have child_sizes := nesting_region_size_eq nested
  simpa only [same, sizes, child_sizes] using
    mergeAt_spec s actual i (by omega) (by omega) (List.getElem?_eq_getElem hs)

theorem simulate_cut (s reference : MarkedTree) (same : s.nesting = reference.nesting)
    (i j : Nat) (ordered : i < j) (valid : j ≤ reference.region.size)
    (proper : j - i < reference.region.size) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = reference.nesting.group i (j - i + 1) ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤ 6 * Real.logb 2 reference.region.size + 2 :=
  ⟨(s.cutInterval i j).1, (s.cutInterval i j).2, cutInterval_simulates s reference same i j ordered valid proper⟩

theorem simulate_merge (s reference child : MarkedTree) (same : s.nesting = reference.nesting)
    (i : Nat) (positive : 0 < reference.region.size) (valid : i ≤ reference.region.size)
    (attached : reference.fringe[i]? = some child) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = reference.nesting.merge i ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤
        8 * Real.logb 2 (reference.region.size + child.region.size : Nat) + 2 :=
  ⟨(s.mergeAt i).1, (s.mergeAt i).2, mergeAt_simulates s reference child same i positive valid attached⟩

end RotationBST.Tango.MarkedTree
