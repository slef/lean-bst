module

public import RotationBST.Tango.State.Nesting.Edits.Transport

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Realize an interval cut specified solely by its before/after nesting.
The cut may lie anywhere inside the current root component. -/
theorem realize_cut (s before after : MarkedTree) (same : s.nesting = before.nesting)
    (cut : ComponentNesting.Cut before.nesting after.nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = after.nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤ 6 * Real.logb 2 before.region.size + 2 := by
  generalize hb : before.nesting = bn at cut
  generalize ha : after.nesting = an at cut
  cases cut with
  | interval a b c nonempty remaining =>
    have sizes := congrArg (fun n : ComponentNesting => n.fringe.length) hb
    rw [nesting_fringe_length] at sizes
    simp only [ComponentNesting.fringe, List.length_append] at sizes
    obtain ⟨t, cost, hn, rotations, bound⟩ := simulate_cut s before same a.length (a.length + b.length - 1)
      (by omega) (by omega) (by omega)
    have count : a.length + b.length - 1 - a.length + 1 = b.length := by omega
    rw [count, hb, ComponentNesting.group_append] at hn
    exact ⟨t, cost, hn, rotations, bound⟩

/-- Reverse an interval cut by merging the corresponding attached component.
The bound depends on the resulting merged auxiliary size. -/
theorem realize_join (s before after : MarkedTree) (same : s.nesting = before.nesting)
    (cut : ComponentNesting.Cut after.nesting before.nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = after.nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤ 8 * Real.logb 2 after.region.size + 2 := by
  generalize hb : before.nesting = bn at cut
  generalize ha : after.nesting = an at cut
  cases cut with
  | interval a b c nonempty remaining =>
    have beforeSize := congrArg (fun n : ComponentNesting => n.fringe.length) hb
    have afterSize := congrArg (fun n : ComponentNesting => n.fringe.length) ha
    rw [nesting_fringe_length] at beforeSize afterSize
    simp only [ComponentNesting.fringe, List.length_append, List.length_singleton] at beforeSize afterSize
    have hi : a.length < before.fringe.length := by rw [marked_fringe_length]; omega
    let child := before.fringe[a.length]'hi
    have mapped : before.fringe.map nesting = a ++ [.branch b] ++ c := by
      rw [← nesting_fringe, hb]; rfl
    have nth : (before.fringe.map nesting)[a.length]? = some (.branch b) := by
      rw [mapped]
      simp [List.append_assoc]
    have childNested : child.nesting = .branch b := by
      simpa only [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq] using nth
    have childSize := congrArg (fun n : ComponentNesting => n.fringe.length) childNested
    rw [nesting_fringe_length] at childSize
    simp only [ComponentNesting.fringe] at childSize
    have total : before.region.size + child.region.size = after.region.size := by omega
    obtain ⟨t, cost, hn, rotations, bound⟩ := simulate_merge s before child same a.length
      (by omega) (by omega) (List.getElem?_eq_getElem hi)
    rw [hb, ComponentNesting.merge_append] at hn
    change t.nesting = .branch (a ++ b ++ c) at hn
    exact ⟨t, cost, hn, rotations, by simpa only [total] using bound⟩

end RotationBST.Tango.MarkedTree
