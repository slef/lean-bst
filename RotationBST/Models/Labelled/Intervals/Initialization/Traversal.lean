module

public import RotationBST.Models.Labelled.Intervals.Initialization.Population
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.IntervalMetadata.Initialization
open Pointer

theorem Run.append {s t u : State} {a b : Nat} (first : Run s t a) (last : Run t u b) : Run s u (a + b) := by
  induction first with
  | refl => simpa using last
  | step first _ ih => simpa only [Nat.add_assoc] using Run.step first (ih last)

private theorem visit_left (l r : Tree) (cs : List Frame) (fields : Nat → Bounds) (pending : Bounds)
    (root : fields (offset cs + l.size) = ⟨offset cs, offset cs + (Tree.node l r).size⟩)
    (child : l ≠ .nil → ∀ (cs : List Frame) (fields : Nat → Bounds), ∃ final,
      Run ⟨⟨l, cs⟩, fields, ⟨offset cs, offset cs + l.size⟩, .write⟩
        ⟨⟨l, cs⟩, populate l (offset cs) fields, final, .up⟩ (work l)) :
    ∃ final, Run ⟨⟨.node l r, cs⟩, fields, pending, .left⟩
      ⟨⟨.node l r, cs⟩, populate l (offset cs) fields, final, .right⟩
      (if l = .nil then 1 else 5 + work l) := by
  cases l with
  | nil => exact ⟨pending, .step rfl .refl⟩
  | node a b =>
    obtain ⟨final, run⟩ := child (by simp) (.left r :: cs) fields
    have enter : tick ⟨⟨.node (.node a b) r, cs⟩, fields, pending, .left⟩ =
        some (4, ⟨⟨.node a b, .left r :: cs⟩, fields, ⟨offset cs, offset cs + (Tree.node a b).size⟩, .write⟩) := by
      simp only [tick, root]
    have leave : Run ⟨⟨.node a b, .left r :: cs⟩, populate (.node a b) (offset cs) fields, final, .up⟩
        ⟨⟨.node (.node a b) r, cs⟩, populate (.node a b) (offset cs) fields, final, .right⟩ 1 :=
      .step rfl .refl
    refine ⟨final, ?_⟩
    have cost : 4 + (work (.node a b) + 1) = 5 + work (.node a b) := by omega
    simpa only [reduceCtorEq, ↓reduceIte, cost] using (Run.step enter (run.append leave))

private theorem visit_right (l r : Tree) (cs : List Frame) (fields : Nat → Bounds) (pending : Bounds)
    (root : fields (offset cs + l.size) = ⟨offset cs, offset cs + (Tree.node l r).size⟩)
    (child : r ≠ .nil → ∀ (cs : List Frame) (fields : Nat → Bounds), ∃ final,
      Run ⟨⟨r, cs⟩, fields, ⟨offset cs, offset cs + r.size⟩, .write⟩
        ⟨⟨r, cs⟩, populate r (offset cs) fields, final, .up⟩ (work r)) :
    ∃ final, Run ⟨⟨.node l r, cs⟩, fields, pending, .right⟩
      ⟨⟨.node l r, cs⟩, populate r (offset cs + l.size + 1) fields, final, .up⟩
      (if r = .nil then 1 else 5 + work r) := by
  cases r with
  | nil => exact ⟨pending, .step rfl .refl⟩
  | node a b =>
    obtain ⟨final, run⟩ := child (by simp) (.right l :: cs) fields
    have enter : tick ⟨⟨.node l (.node a b), cs⟩, fields, pending, .right⟩ =
        some (4, ⟨⟨.node a b, .right l :: cs⟩, fields,
          ⟨offset (.right l :: cs), offset (.right l :: cs) + (Tree.node a b).size⟩, .write⟩) := by
      simp only [tick, root, offset, Tree.size, Nat.add_assoc]
    have leave : Run ⟨⟨.node a b, .right l :: cs⟩, populate (.node a b) (offset (.right l :: cs)) fields, final, .up⟩
        ⟨⟨.node l (.node a b), cs⟩, populate (.node a b) (offset (.right l :: cs)) fields, final, .up⟩ 1 :=
      .step rfl .refl
    refine ⟨final, ?_⟩
    have cost : 4 + (work (.node a b) + 1) = 5 + work (.node a b) := by omega
    simpa only [reduceCtorEq, ↓reduceIte, offset, cost] using (Run.step enter (run.append leave))

/-- A local traversal initializes a nonempty subtree and returns to its root.
No recursion stack is part of the machine; induction only proves the run. -/
theorem traversal (tree : Tree) (nonempty : tree ≠ .nil) (cs : List Frame) (fields : Nat → Bounds) :
    ∃ final, Run ⟨⟨tree, cs⟩, fields, ⟨offset cs, offset cs + tree.size⟩, .write⟩
      ⟨⟨tree, cs⟩, populate tree (offset cs) fields, final, .up⟩ (work tree) := by
  induction tree generalizing cs fields with
  | nil => exact False.elim (nonempty rfl)
  | node l r il ir =>
    let rootFields := Function.update fields (offset cs + l.size) (Bounds.mk (offset cs) (offset cs + (Tree.node l r).size))
    have root : rootFields (offset cs + l.size) = ⟨offset cs, offset cs + (Tree.node l r).size⟩ := Function.update_self _ _ _
    obtain ⟨leftPending, leftRun⟩ := visit_left l r cs rootFields ⟨offset cs, offset cs + (Tree.node l r).size⟩ root il
    have rootStill : populate l (offset cs) rootFields (offset cs + l.size) =
        ⟨offset cs, offset cs + (Tree.node l r).size⟩ :=
      (populate_outside l (offset cs) rootFields _ (Or.inr le_rfl)).trans root
    obtain ⟨final, rightRun⟩ := visit_right l r cs (populate l (offset cs) rootFields) leftPending rootStill ir
    refine ⟨final, ?_⟩
    simpa only [work, populate, rootFields, Nat.add_assoc] using
      Run.step (show tick ⟨⟨.node l r, cs⟩, fields, ⟨offset cs, offset cs + (Tree.node l r).size⟩, .write⟩ =
        some (2, ⟨⟨.node l r, cs⟩, rootFields, ⟨offset cs, offset cs + (Tree.node l r).size⟩, .left⟩) from rfl)
        (leftRun.append rightRun)

end RotationBST.IntervalMetadata.Initialization
