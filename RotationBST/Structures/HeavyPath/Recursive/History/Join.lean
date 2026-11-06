module

public import RotationBST.Structures.HeavyPath.Recursive.History.Push
public import RotationBST.Structures.HeavyPath.Recursive.History.Preservation
public import RotationBST.Structures.HeavyPath.Paired.Population.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History
open Paired LabelledCursor

/-- Reassemble a source root from two arbitrary recursive histories. Only the
heavy child's outer pair is updated; all payload occurrences keep their credits. -/
theorem layout_join_within {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {a b : Tree} {leftCredit rightCredit : Nat}
    (left : Layout weight l a leftCredit) (right : Layout weight r b rightCredit)
    (keyPositive : 0 < weight x) :
    ∃ (shape : Tree) (credit cost : Nat), Layout weight (.node l x r) shape credit ∧
      Pointer.TraceWithin (fun t => t.size = (Tree.node a b).size ∧
        ∀ x, Tree.depth t x ≤ 4 * Tree.depth (.node a b) x + 16) ⟨.node a b, []⟩ ⟨shape, []⟩ cost ∧
      cost + credit ≤ 24 + leftCredit + rightCredit ∧
      (cost : ℝ) ≤ 10 + 14 * Real.logb 2 (Tree.node a b).size := by
  classical
  have positive : Positive weight (.node l x r) := ⟨layout_positive left, keyPositive, layout_positive right⟩
  by_cases heavy : LeftHeavy weight l r
  · by_cases empty : l = .nil
    · have rightEmpty : r = .nil := by
        by_contra hn
        have rightPositive := HeavyPath.Results.mass_positive positive.2.2 hn
        change mass weight r ≤ mass weight l at heavy
        rw [empty, mass] at heavy
        linarith
      subst l; subst r
      have aEmpty : a = .nil := by
        have size := layout_size left
        cases a <;> simp_all [Tree.size, LabelledTree.erase]
      have bEmpty : b = .nil := by
        have size := layout_size right
        cases b <;> simp_all [Tree.size, LabelledTree.erase]
      subst a; subst b
      have valid : PathValid weight ([] : List (Entry α)) Stacks.empty :=
        ⟨Paired.Results.empty_valid, rfl, rfl⟩
      have context : ([] : List (Entry α)).map Entry.source = (extract weight (.node .nil x .nil)).context := by
        simp [extract, LeftHeavy, mass]
      have layout := Layout.path positive (by intro h; cases h) context valid (by intro e he; cases he)
      refine ⟨Stacks.empty.tree, 0, 0, ?_, .refl ⟨rfl, by intro x; simp only [Pointer.Config.tree, Pointer.plug]; omega⟩, by omega, by simp [Tree.size]⟩
      exact layout
    · cases left with
      | nil => exact False.elim (empty rfl)
      | @path _ es p childPositive childNonempty context valid children =>
        let e : Entry α := ⟨.left x r, b, rightCredit⟩
        have nonnegative : 0 ≤ frameMass weight e.source :=
          add_nonneg keyPositive.le (mass_nonnegative (positive_nonnegative (layout_positive right)))
        obtain ⟨nextValid, trace, bound⟩ := push_path_within valid e nonnegative
        have nextContext : (es ++ [e]).map Entry.source = (extract weight (.node l x r)).context := by
          simp only [List.map_append, List.map_cons, List.map_nil, context]
          simp only [extract, heavy, childNonempty, ite_true, ite_false, extend, e]
        have nextChildren : ∀ f ∈ es ++ [e], Layout weight (framePayload f.source) f.shape f.credit := by
          intro f hf
          rcases List.mem_append.mp hf with earlier | last
          · exact children f earlier
          · rcases List.mem_singleton.mp last with rfl
            exact right
        have layout := Layout.path positive (by intro h; cases h) nextContext nextValid nextChildren
        have worst := Paired.Population.push_cost_bound valid.pair e.source
          (n := (Tree.node p.tree b).size) (by simp only [Tree.size]; omega)
        refine ⟨_, _, p.pushCost e.source + 1, layout, trace, ?_, ?_⟩
        · simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
            List.sum_nil, Nat.add_zero, e]
          simp only [e] at bound
          omega
        · simpa only [Nat.cast_add, Nat.cast_one] using worst
  · have nonempty : r ≠ .nil := by
      intro empty
      apply heavy
      change mass weight r ≤ mass weight l
      simpa only [empty, mass] using mass_nonnegative (positive_nonnegative positive.1)
    cases right with
    | nil => exact False.elim (nonempty rfl)
    | @path _ es p childPositive childNonempty context valid children =>
      let e : Entry α := ⟨.right l x, a, leftCredit⟩
      have nonnegative : 0 ≤ frameMass weight e.source :=
        add_nonneg (mass_nonnegative (positive_nonnegative (layout_positive left))) keyPositive.le
      obtain ⟨nextValid, trace, bound⟩ := push_path_within valid e nonnegative
      have nextContext : (es ++ [e]).map Entry.source = (extract weight (.node l x r)).context := by
        simp only [List.map_append, List.map_cons, List.map_nil, context]
        simp only [extract, heavy, childNonempty, ite_false, extend, e]
      have nextChildren : ∀ f ∈ es ++ [e], Layout weight (framePayload f.source) f.shape f.credit := by
        intro f hf
        rcases List.mem_append.mp hf with earlier | last
        · exact children f earlier
        · rcases List.mem_singleton.mp last with rfl
          exact left
      have layout := Layout.path positive (by intro h; cases h) nextContext nextValid nextChildren
      have worst := Paired.Population.push_cost_bound valid.pair e.source
        (n := (Tree.node a p.tree).size) (by simp only [Tree.size]; omega)
      refine ⟨_, _, p.pushCost e.source + 1, layout, trace, ?_, ?_⟩
      · simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil, Nat.add_zero, e]
        simp only [e] at bound
        omega
      · simpa only [Nat.cast_add, Nat.cast_one] using worst

theorem layout_join_bounded {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {a b : Tree} {leftCredit rightCredit : Nat}
    (left : Layout weight l a leftCredit) (right : Layout weight r b rightCredit)
    (keyPositive : 0 < weight x) :
    ∃ (shape : Tree) (credit cost : Nat), Layout weight (.node l x r) shape credit ∧
      Pointer.Trace ⟨.node a b, []⟩ ⟨shape, []⟩ cost ∧
      cost + credit ≤ 24 + leftCredit + rightCredit ∧
      (cost : ℝ) ≤ 10 + 14 * Real.logb 2 (Tree.node a b).size := by
  obtain ⟨shape, credit, cost, layout, trace, amortized, worst⟩ := layout_join_within left right keyPositive
  exact ⟨shape, credit, cost, layout, trace.trace, amortized, worst⟩

/-- Retain the original joining interface with the same bounded witness. -/
theorem layout_join {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {a b : Tree} {leftCredit rightCredit : Nat}
    (left : Layout weight l a leftCredit) (right : Layout weight r b rightCredit)
    (keyPositive : 0 < weight x) :
    ∃ (shape : Tree) (credit cost : Nat), Layout weight (.node l x r) shape credit ∧
      Pointer.Trace ⟨.node a b, []⟩ ⟨shape, []⟩ cost ∧
      cost + credit ≤ 24 + leftCredit + rightCredit := by
  obtain ⟨shape, credit, cost, layout, trace, amortized, _⟩ := layout_join_bounded left right keyPositive
  exact ⟨shape, credit, cost, layout, trace, amortized⟩

end RotationBST.HeavyPath.Recursive.History
