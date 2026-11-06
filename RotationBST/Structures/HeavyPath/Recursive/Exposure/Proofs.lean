module

public import RotationBST.Structures.HeavyPath.Paired.Exposure.Abstract
public import RotationBST.Structures.HeavyPath.Recursive.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.Exposure
open Paired LabelledCursor

theorem rootPair_represents {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) :
    (rootPair weight t).Represents weight (rebuild weight) (extract weight t).context := by
  apply Paired.Exposure.build_represents
  intro frame member
  exact ((HeavyPath.Results.extract_positive positive).2 frame member).le

theorem represented_size {α : Type} {weight : α → ℝ} {t : LabelledTree α} {p : Stacks}
    (positive : Positive weight t) (nonempty : t ≠ .nil)
    (represented : p.Represents weight (rebuild weight) (extract weight t).context) :
    p.tree.size = t.erase.size := by
  have sizes := (Paired.Exposure.represents_sizes represented (rootPair_represents positive)).2.2
  have source := (Recursive.Results.rootPair_source positive nonempty).2.2
  rw [← source, Recursive.Results.rebuild_size positive] at sizes
  exact sizes

theorem expose_left {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    (positive : Positive weight (.node l x r)) (heavy : LeftHeavy weight l r) (nonempty : l ≠ .nil) :
    ∃ rest : Stacks,
      rest.Represents weight (rebuild weight) (extract weight l).context ∧
      Pointer.Trace ⟨rebuild weight (.node l x r), []⟩
        ⟨.node rest.tree (rebuild weight r), []⟩ ((rootPair weight (.node l x r)).exposeCost (.left x r)) ∧
      (rootPair weight (.node l x r)).exposeCost (.left x r) + rest.potential ≤
        24 + (rootPair weight (.node l x r)).potential ∧
      rest.tree.size = l.erase.size ∧
      (rootPair weight (.node l x r)).mass = rest.mass + (weight x + mass weight r) := by
  have path : (extract weight (.node l x r)).context = (extract weight l).context ++ [.left x r] := by
    classical
    simp only [extract, heavy, nonempty, ite_true, ite_false, extend]
  have rep := rootPair_represents positive
  rw [path] at rep
  obtain ⟨rest, represented, trace, bound, mass⟩ := Paired.Exposure.expose_frame rep
  have source := (Recursive.Results.rootPair_source positive (by intro h; cases h)).2.2
  refine ⟨rest, represented, ?_, bound, represented_size positive.1 nonempty represented, mass⟩
  simpa only [source, replaceFrame, Pointer.plug] using trace

theorem expose_right {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    (positive : Positive weight (.node l x r)) (heavy : ¬ LeftHeavy weight l r) (nonempty : r ≠ .nil) :
    ∃ rest : Stacks,
      rest.Represents weight (rebuild weight) (extract weight r).context ∧
      Pointer.Trace ⟨rebuild weight (.node l x r), []⟩
        ⟨.node (rebuild weight l) rest.tree, []⟩ ((rootPair weight (.node l x r)).exposeCost (.right l x)) ∧
      (rootPair weight (.node l x r)).exposeCost (.right l x) + rest.potential ≤
        24 + (rootPair weight (.node l x r)).potential ∧
      rest.tree.size = r.erase.size ∧
      (rootPair weight (.node l x r)).mass = rest.mass + (mass weight l + weight x) := by
  have path : (extract weight (.node l x r)).context = (extract weight r).context ++ [.right l x] := by
    classical
    simp only [extract, heavy, nonempty, ite_false, extend]
  have rep := rootPair_represents positive
  rw [path] at rep
  obtain ⟨rest, represented, trace, bound, mass⟩ := Paired.Exposure.expose_frame rep
  have source := (Recursive.Results.rootPair_source positive (by intro h; cases h)).2.2
  refine ⟨rest, represented, ?_, bound, represented_size positive.2.2 nonempty represented, mass⟩
  simpa only [source, replaceFrame, Pointer.plug] using trace

/-- Every nonempty recursive layout exposes its original source root. The
potential of the remaining heavy path is retained in the cost certificate. -/
theorem root_exposure {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    (positive : Positive weight (.node l x r)) :
    ∃ (a b : Tree) (cost remainingPotential : Nat),
      Pointer.Trace ⟨rebuild weight (.node l x r), []⟩ ⟨.node a b, []⟩ cost ∧
      a.size = l.erase.size ∧ b.size = r.erase.size ∧
      (Pointer.Config.mk (.node a b) []).key? = some l.erase.size ∧
      cost + remainingPotential ≤ 24 + (rootPair weight (.node l x r)).potential := by
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
      refine ⟨.nil, .nil, 0, (rootPair weight (.node .nil x .nil)).potential, ?_, rfl, rfl, rfl, by omega⟩
      have source := (Recursive.Results.rootPair_source positive (by intro h; cases h)).2.2
      rw [source]
      have eq : (rootPair weight (.node .nil x .nil)).tree = .node .nil .nil := by
        simp [rootPair, extract, LeftHeavy, mass, Stacks.buildWith, Stacks.tree, Stacks.empty,
          PopTart.Chocolate.Layer.decode, PopTart.Chocolate.Regulars.attach, PopTart.Chocolate.Icing.decode,
          PopTart.WeightedTree.tree, PopTart.WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree, Tree.mirror]
      rw [eq]
      exact .refl
    · obtain ⟨rest, _, trace, bound, size, _⟩ := expose_left positive heavy empty
      refine ⟨rest.tree, rebuild weight r, _, rest.potential, trace, size,
        Recursive.Results.rebuild_size positive.2.2, ?_, bound⟩
      simpa only [Pointer.Config.key?, Pointer.offset, Nat.zero_add] using congrArg some size
  · have nonempty : r ≠ .nil := by
      intro empty
      have leftMass := HeavyPath.mass_nonnegative (HeavyPath.positive_nonnegative positive.1)
      apply heavy
      change mass weight r ≤ mass weight l
      simpa only [empty, mass] using leftMass
    obtain ⟨rest, _, trace, bound, size, _⟩ := expose_right positive heavy nonempty
    refine ⟨rebuild weight l, rest.tree, _, rest.potential, trace,
      Recursive.Results.rebuild_size positive.1, size, ?_, bound⟩
    simpa only [Pointer.Config.key?, Pointer.offset, Nat.zero_add] using
      congrArg some (Recursive.Results.rebuild_size positive.1)

end RotationBST.HeavyPath.Recursive.Exposure
