module

public import RotationBST.Structures.HeavyPath.Finger.Transfer.Exposure.Compose
public import RotationBST.Structures.HeavyPath.Recursive.Exposure.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.Transfer.Exposure
open PopTart Recursive

/-- The child may be a residual path left by earlier exposures; fresh
canonical assembly is not required. -/
theorem downLeft_pair {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} {child : Paired.Stacks} (valid : p.Valid) (positive : Positive weight (.node l x r))
    (represented : child.Represents weight (rebuild weight) (extract weight (.node l x r)).context)
    {oldCharge : ℝ} (stored : p.lower.top = .leaf child.tree.mirror oldCharge)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    ∃ (view : Recursive.Exposure.View) (cost : Nat), view.Valid weight l r ∧
      let next := p.downLeft (view.leftTree weight l) (view.rightTree weight r) lowerCharge upperCharge
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + view.potential ≤ 54 + p.potential + child.potential ∧
      next.mass + oldCharge = p.mass + lowerCharge + upperCharge ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size - r.erase.size - 1) := by
  obtain ⟨view, exposureCost, viewValid, exposure, _, rightSize, exposureBound⟩ :=
    Recursive.Exposure.Results.expose_pair_view positive represented
  obtain ⟨cost, trace, bound, nextValid, mass, rank⟩ :=
    downLeft_exposed valid stored exposure lowerNonnegative upperNonnegative
  rw [rightSize] at rank
  exact ⟨view, cost, viewValid, trace, nextValid, by omega, mass, rank⟩

theorem downRight_pair {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} {child : Paired.Stacks} (valid : p.Valid) (positive : Positive weight (.node l x r))
    (represented : child.Represents weight (rebuild weight) (extract weight (.node l x r)).context)
    {oldCharge : ℝ} (stored : p.upper.top = .leaf child.tree oldCharge)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    ∃ (view : Recursive.Exposure.View) (cost : Nat), view.Valid weight l r ∧
      let next := p.downRight (view.leftTree weight l) (view.rightTree weight r) lowerCharge upperCharge
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + view.potential ≤ 54 + p.potential + child.potential ∧
      next.mass + oldCharge = p.mass + lowerCharge + upperCharge ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size + l.erase.size + 1) := by
  obtain ⟨view, exposureCost, viewValid, exposure, leftSize, _, exposureBound⟩ :=
    Recursive.Exposure.Results.expose_pair_view positive represented
  obtain ⟨cost, trace, bound, nextValid, mass, rank⟩ :=
    downRight_exposed valid stored exposure lowerNonnegative upperNonnegative
  rw [leftSize] at rank
  exact ⟨view, cost, viewValid, trace, nextValid, by omega, mass, rank⟩

/-- Enter a recursively represented left child, retaining the actual exposed
view and the potential of its residual heavy path in the output certificate. -/
theorem downLeft_recursive {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) (positive : Positive weight (.node l x r)) {oldCharge : ℝ}
    (stored : p.lower.top = .leaf (rebuild weight (.node l x r)).mirror oldCharge)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    ∃ (view : Recursive.Exposure.View) (cost : Nat), view.Valid weight l r ∧
      let next := p.downLeft (view.leftTree weight l) (view.rightTree weight r) lowerCharge upperCharge
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + view.potential ≤ 54 + p.potential + (rootPair weight (.node l x r)).potential ∧
      next.mass + oldCharge = p.mass + lowerCharge + upperCharge ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size - r.erase.size - 1) := by
  obtain ⟨view, exposureCost, viewValid, exposure, _, rightSize, exposureBound⟩ :=
    Recursive.Exposure.Results.expose_view positive
  obtain ⟨cost, trace, bound, nextValid, mass, rank⟩ :=
    downLeft_exposed valid stored exposure lowerNonnegative upperNonnegative
  rw [rightSize] at rank
  exact ⟨view, cost, viewValid, trace, nextValid, by omega, mass, rank⟩

theorem downRight_recursive {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) (positive : Positive weight (.node l x r)) {oldCharge : ℝ}
    (stored : p.upper.top = .leaf (rebuild weight (.node l x r)) oldCharge)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    ∃ (view : Recursive.Exposure.View) (cost : Nat), view.Valid weight l r ∧
      let next := p.downRight (view.leftTree weight l) (view.rightTree weight r) lowerCharge upperCharge
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + view.potential ≤ 54 + p.potential + (rootPair weight (.node l x r)).potential ∧
      next.mass + oldCharge = p.mass + lowerCharge + upperCharge ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size + l.erase.size + 1) := by
  obtain ⟨view, exposureCost, viewValid, exposure, leftSize, _, exposureBound⟩ :=
    Recursive.Exposure.Results.expose_view positive
  obtain ⟨cost, trace, bound, nextValid, mass, rank⟩ :=
    downRight_exposed valid stored exposure lowerNonnegative upperNonnegative
  rw [leftSize] at rank
  exact ⟨view, cost, viewValid, trace, nextValid, by omega, mass, rank⟩

/-- Shift the departing finger's weight into the receiving stack and release
the arriving source root's weight from its old payload charge. -/
theorem downLeft_source {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) (positive : Positive weight (.node l x r))
    {carry fingerWeight : ℝ} (carryNonnegative : 0 ≤ carry) (fingerNonnegative : 0 ≤ fingerWeight)
    (stored : p.lower.top = .leaf (rebuild weight (.node l x r)).mirror (carry + mass weight (.node l x r))) :
    ∃ (view : Recursive.Exposure.View) (cost : Nat), view.Valid weight l r ∧
      let next := p.downLeft (view.leftTree weight l) (view.rightTree weight r)
        (carry + mass weight l) (fingerWeight + mass weight r)
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + view.potential ≤ 54 + p.potential + (rootPair weight (.node l x r)).potential ∧
      next.mass + weight x = p.mass + fingerWeight ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size - r.erase.size - 1) := by
  have leftNN := HeavyPath.mass_nonnegative (HeavyPath.positive_nonnegative positive.1)
  have rightNN := HeavyPath.mass_nonnegative (HeavyPath.positive_nonnegative positive.2.2)
  obtain ⟨view, cost, viewValid, trace, nextValid, bound, balance, rank⟩ :=
    downLeft_recursive valid positive stored (add_nonneg carryNonnegative leftNN)
      (add_nonneg fingerNonnegative rightNN)
  refine ⟨view, cost, viewValid, trace, nextValid, bound, ?_, rank⟩
  simp only [mass] at balance
  linarith

theorem downRight_source {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) (positive : Positive weight (.node l x r))
    {carry fingerWeight : ℝ} (carryNonnegative : 0 ≤ carry) (fingerNonnegative : 0 ≤ fingerWeight)
    (stored : p.upper.top = .leaf (rebuild weight (.node l x r)) (carry + mass weight (.node l x r))) :
    ∃ (view : Recursive.Exposure.View) (cost : Nat), view.Valid weight l r ∧
      let next := p.downRight (view.leftTree weight l) (view.rightTree weight r)
        (fingerWeight + mass weight l) (carry + mass weight r)
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + view.potential ≤ 54 + p.potential + (rootPair weight (.node l x r)).potential ∧
      next.mass + weight x = p.mass + fingerWeight ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size + l.erase.size + 1) := by
  have leftNN := HeavyPath.mass_nonnegative (HeavyPath.positive_nonnegative positive.1)
  have rightNN := HeavyPath.mass_nonnegative (HeavyPath.positive_nonnegative positive.2.2)
  obtain ⟨view, cost, viewValid, trace, nextValid, bound, balance, rank⟩ :=
    downRight_recursive valid positive stored (add_nonneg fingerNonnegative leftNN)
      (add_nonneg carryNonnegative rightNN)
  refine ⟨view, cost, viewValid, trace, nextValid, bound, ?_, rank⟩
  simp only [mass] at balance
  linarith

end RotationBST.HeavyPath.Finger.Transfer.Exposure
