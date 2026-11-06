module

public import RotationBST.Structures.HeavyPath.Recursive.Exposure.Definitions.Abstract
public import RotationBST.Structures.HeavyPath.Recursive.Exposure.Proofs
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.Exposure
open Paired

/-- Expose a root from any valid representation of its extracted path,
including a residual pair produced by earlier pops. -/
theorem expose_pair_view {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α} {p : Stacks}
    (positive : Positive weight (.node l x r))
    (represented : p.Represents weight (rebuild weight) (extract weight (.node l x r)).context) :
    ∃ (view : View) (cost : Nat), view.Valid weight l r ∧
      Pointer.Trace ⟨p.tree, []⟩
        ⟨.node (view.leftTree weight l) (view.rightTree weight r), []⟩ cost ∧
      (view.leftTree weight l).size = l.erase.size ∧
      (view.rightTree weight r).size = r.erase.size ∧
      cost + view.potential ≤ 24 + p.potential := by
  classical
  by_cases heavy : LeftHeavy weight l r
  · by_cases empty : l = .nil
    · have rightEmpty : r = .nil := by
        by_contra hn
        have rightPositive := HeavyPath.Results.mass_positive positive.2.2 hn
        change mass weight r ≤ mass weight l at heavy
        rw [empty, mass] at heavy
        linarith
      subst l; subst r
      have size := represented_size positive (by intro h; cases h) represented
      simp only [Stacks.tree, Tree.size, Tree.mirror_size, LabelledTree.erase] at size
      have leftEmpty : p.lower.decode.tree = .nil := by
        cases h : p.lower.decode.tree <;> simp_all [Tree.size]
        omega
      have rightEmpty : p.upper.decode.tree = .nil := by
        cases h : p.upper.decode.tree <;> simp_all [Tree.size]
      refine ⟨.leaf, 0, ⟨rfl, rfl⟩, ?_, rfl, rfl, by simp [View.potential]⟩
      simpa only [Stacks.tree, leftEmpty, rightEmpty, Tree.mirror, View.leftTree, View.rightTree]
        using (Pointer.Trace.refl (c := Pointer.Config.mk p.tree []))
    · have path : (extract weight (.node l x r)).context =
          (extract weight l).context ++ [.left x r] := by
        simp only [extract, heavy, empty, ite_true, ite_false, extend]
      rw [path] at represented
      obtain ⟨rest, restRep, trace, bound, _⟩ := Paired.Exposure.Results.expose_frame represented
      refine ⟨.left rest, _, ⟨heavy, empty, restRep⟩, ?_,
        represented_size positive.1 empty restRep, Recursive.Results.rebuild_size positive.2.2, bound⟩
      simpa only [View.leftTree, View.rightTree, replaceFrame, Pointer.plug] using trace
  · have nonempty : r ≠ .nil := by
      intro empty
      have leftMass := HeavyPath.mass_nonnegative (HeavyPath.positive_nonnegative positive.1)
      apply heavy
      change mass weight r ≤ mass weight l
      simpa only [empty, mass] using leftMass
    have path : (extract weight (.node l x r)).context =
        (extract weight r).context ++ [.right l x] := by
      simp only [extract, heavy, nonempty, ite_false, extend]
    rw [path] at represented
    obtain ⟨rest, restRep, trace, bound, _⟩ := Paired.Exposure.Results.expose_frame represented
    refine ⟨.right rest, _, ⟨heavy, nonempty, restRep⟩, ?_,
      Recursive.Results.rebuild_size positive.1, represented_size positive.2.2 nonempty restRep, bound⟩
    simpa only [View.leftTree, View.rightTree, replaceFrame, Pointer.plug] using trace

/-- The output keeps the residual stack, so its credit can be included in a
subsequent simulation state rather than discarded after this operation. -/
theorem expose_view {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    (positive : Positive weight (.node l x r)) :
    ∃ (view : View) (cost : Nat), view.Valid weight l r ∧
      Pointer.Trace ⟨rebuild weight (.node l x r), []⟩
        ⟨.node (view.leftTree weight l) (view.rightTree weight r), []⟩ cost ∧
      (view.leftTree weight l).size = l.erase.size ∧
      (view.rightTree weight r).size = r.erase.size ∧
      cost + view.potential ≤ 24 + (rootPair weight (.node l x r)).potential := by
  have exposed := expose_pair_view positive (rootPair_represents positive)
  have source := (Recursive.Results.rootPair_source positive (by intro h; cases h)).2.2
  simpa only [source] using exposed

end RotationBST.HeavyPath.Recursive.Exposure
