module

public import RotationBST.Structures.HeavyPath.Recursive.History.Pop
public import RotationBST.Structures.HeavyPath.Recursive.History.Depth
public import RotationBST.Structures.HeavyPath.Paired.Population.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History
open Paired LabelledCursor

private theorem split_last {α : Type} {es : List (Entry α)} {cs : List (Frame α)} {f : Frame α}
    (context : es.map Entry.source = cs ++ [f]) :
    ∃ earlier e, es = earlier ++ [e] ∧ earlier.map Entry.source = cs ∧ e.source = f := by
  obtain ⟨earlier, suffix, split, first, last⟩ := List.map_eq_append_iff.mp context
  obtain ⟨e, rfl, source⟩ := List.map_eq_singleton_iff.mp last
  exact ⟨earlier, e, split, first, source⟩

/-- Source-root exposure preserves recursively valid child layouts and
accounts for every nested potential in both children. -/
theorem layout_expose_within {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {shape : Tree} {credit : Nat} (layout : Layout weight (.node l x r) shape credit) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Layout weight l a leftCredit ∧ Layout weight r b rightCredit ∧
      Pointer.TraceWithin (fun t => t.size = shape.size ∧
        ∀ x, Tree.depth t x ≤ 4 * Tree.depth shape x + 10) ⟨shape, []⟩ ⟨.node a b, []⟩ cost ∧
      cost + leftCredit + rightCredit ≤ 24 + credit ∧
      (cost : ℝ) ≤ 10 + 10 * Real.logb 2 shape.size := by
  classical
  cases layout with
  | @path _ es p positive nonempty context valid children =>
    by_cases heavy : LeftHeavy weight l r
    · by_cases empty : l = .nil
      · have rightEmpty : r = .nil := by
          by_contra hn
          have rightPositive := HeavyPath.Results.mass_positive positive.2.2 hn
          change mass weight r ≤ mass weight l at heavy
          rw [empty, mass] at heavy
          linarith
        subst l; subst r
        have size := path_size positive nonempty context valid (fun e member => layout_size (children e member))
        simp only [Stacks.tree, Tree.size, Tree.mirror_size, LabelledTree.erase] at size
        have lowerEmpty : p.lower.decode.tree = .nil := by
          cases h : p.lower.decode.tree <;> simp_all [Tree.size]
          omega
        have upperEmpty : p.upper.decode.tree = .nil := by
          cases h : p.upper.decode.tree <;> simp_all [Tree.size]
        refine ⟨.nil, .nil, 0, 0, 0, .nil, .nil, ?_, by omega, ?_⟩
        · have fixed : Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
              ∀ x, Tree.depth t x ≤ 4 * Tree.depth p.tree x + 10)
              ⟨p.tree, []⟩ ⟨p.tree, []⟩ 0 := .refl ⟨rfl, by intro x; simp only [Pointer.Config.tree, Pointer.plug]; omega⟩
          simpa only [Stacks.tree, lowerEmpty, upperEmpty, Tree.mirror] using fixed
        · simp [Stacks.tree, lowerEmpty, upperEmpty, Tree.size, Tree.mirror]
      · have path : (extract weight (.node l x r)).context = (extract weight l).context ++ [.left x r] := by
          simp only [extract, heavy, empty, ite_true, ite_false, extend]
        rw [path] at context
        obtain ⟨earlier, e, rfl, prefixContext, source⟩ := split_last context
        obtain ⟨rest, restValid, trace, bound⟩ := pop_path_within valid
        have light := children e (by simp)
        have rightLayout : Layout weight r e.shape e.credit := by
          simpa only [source, framePayload] using light
        have leftLayout : Layout weight l rest.tree (rest.potential + (earlier.map Entry.credit).sum) :=
          .path positive.1 empty prefixContext restValid (fun f member => children f (by simp [member]))
        refine ⟨rest.tree, e.shape, _, _, p.exposeCost e.source, leftLayout, rightLayout, ?_, ?_,
          Paired.Population.expose_cost_bound valid.pair e.source le_rfl⟩
        · simpa only [Entry.wrap, source] using trace
        · simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
            List.sum_cons, List.sum_nil, Nat.add_zero]
          omega
    · have rightNonempty : r ≠ .nil := by
        intro empty
        have leftMass := HeavyPath.mass_nonnegative (HeavyPath.positive_nonnegative positive.1)
        apply heavy
        change mass weight r ≤ mass weight l
        simpa only [empty, mass] using leftMass
      have path : (extract weight (.node l x r)).context = (extract weight r).context ++ [.right l x] := by
        simp only [extract, heavy, rightNonempty, ite_false, extend]
      rw [path] at context
      obtain ⟨earlier, e, rfl, prefixContext, source⟩ := split_last context
      obtain ⟨rest, restValid, trace, bound⟩ := pop_path_within valid
      have light := children e (by simp)
      have leftLayout : Layout weight l e.shape e.credit := by
        simpa only [source, framePayload] using light
      have rightLayout : Layout weight r rest.tree (rest.potential + (earlier.map Entry.credit).sum) :=
        .path positive.2.2 rightNonempty prefixContext restValid (fun f member => children f (by simp [member]))
      refine ⟨e.shape, rest.tree, _, _, p.exposeCost e.source, leftLayout, rightLayout, ?_, ?_,
          Paired.Population.expose_cost_bound valid.pair e.source le_rfl⟩
      · simpa only [Entry.wrap, source] using trace
      · simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil, Nat.add_zero]
        omega

theorem layout_expose_bounded {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {shape : Tree} {credit : Nat} (layout : Layout weight (.node l x r) shape credit) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Layout weight l a leftCredit ∧ Layout weight r b rightCredit ∧
      Pointer.Trace ⟨shape, []⟩ ⟨.node a b, []⟩ cost ∧
      cost + leftCredit + rightCredit ≤ 24 + credit ∧
      (cost : ℝ) ≤ 10 + 10 * Real.logb 2 shape.size := by
  obtain ⟨a, b, lc, rc, cost, left, right, trace, amortized, worst⟩ := layout_expose_within layout
  exact ⟨a, b, lc, rc, cost, left, right, trace.trace, amortized, worst⟩

/-- The original interface is a projection of the joint amortized and
worst-case certificate, using the same representation and physical trace. -/
theorem layout_expose {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {shape : Tree} {credit : Nat} (layout : Layout weight (.node l x r) shape credit) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Layout weight l a leftCredit ∧ Layout weight r b rightCredit ∧
      Pointer.Trace ⟨shape, []⟩ ⟨.node a b, []⟩ cost ∧
      cost + leftCredit + rightCredit ≤ 24 + credit := by
  obtain ⟨a, b, lc, rc, cost, left, right, trace, amortized, _⟩ := layout_expose_bounded layout
  exact ⟨a, b, lc, rc, cost, left, right, trace, amortized⟩

end RotationBST.HeavyPath.Recursive.History
