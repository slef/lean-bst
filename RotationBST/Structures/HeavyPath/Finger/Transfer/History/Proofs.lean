module

public import RotationBST.Structures.HeavyPath.Recursive.History.Abstract
public import RotationBST.Structures.HeavyPath.Finger.Transfer.Exposure.Abstract
public import RotationBST.Structures.HeavyPath.Finger.Transfer.Interruption.Exposure
public import RotationBST.Structures.HeavyPath.Finger.Population.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.Transfer.History
open Recursive

/-- A left move preserves the full recursively valid histories of both new
payloads, with every nested potential included in the amortized certificate. -/
theorem downLeft_within {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) {shape : Tree} {childCredit : Nat}
    (child : Recursive.History.Layout weight (.node l x r) shape childCredit)
    {carry fingerWeight : ℝ} (carryNonnegative : 0 ≤ carry) (fingerNonnegative : 0 ≤ fingerWeight)
    (stored : p.lower.top = .leaf shape.mirror (carry + mass weight (.node l x r))) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Recursive.History.Layout weight l a leftCredit ∧ Recursive.History.Layout weight r b rightCredit ∧
      let next := p.downLeft a b (carry + mass weight l) (fingerWeight + mass weight r)
      Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
        ∀ x, Tree.depth t x ≤ 16 * Tree.depth p.tree x + 64) ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + leftCredit + rightCredit ≤ 54 + p.potential + childCredit ∧
      next.mass + weight x = p.mass + fingerWeight ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size - r.erase.size - 1) ∧
      (cost : ℝ) ≤ 26 + 24 * Real.logb 2 p.tree.size := by
  have positive := Recursive.History.Results.layout_positive child
  have leftNN := HeavyPath.mass_nonnegative (HeavyPath.positive_nonnegative positive.1)
  have rightNN := HeavyPath.mass_nonnegative (HeavyPath.positive_nonnegative positive.2.2)
  obtain ⟨a, b, leftCredit, rightCredit, exposureCost, left, right, exposure, exposureBound, exposureWorst⟩ :=
    Recursive.History.Results.layout_expose_within child
  obtain ⟨cost, trace, bound, nextValid, balance, rank, work⟩ := Interruption.downLeft_exposed_within valid stored exposure
    (add_nonneg carryNonnegative leftNN) (add_nonneg fingerNonnegative rightNN)
  rw [Recursive.History.Results.layout_size right] at rank
  refine ⟨a, b, leftCredit, rightCredit, cost, left, right, trace, nextValid, by omega, ?_, rank, ?_⟩
  · simp only [mass] at balance
    linarith
  · have size := Population.Results.lower_payload_size stored
    have positiveSize : 0 < shape.size := by
      rw [Recursive.History.Results.layout_size child]
      simp only [LabelledTree.erase, Tree.size]
      omega
    have logarithm : Real.logb 2 shape.size ≤ Real.logb 2 p.tree.size := by
      apply Real.logb_le_logb_of_le (by norm_num)
      · exact_mod_cast positiveSize
      · exact_mod_cast size
    have stackWorst := Population.Results.upper_push valid
    have workReal : (cost : ℝ) ≤ exposureCost + p.upper.pushCost + 10 := by
      exact_mod_cast work
    linarith

theorem downLeft_bounded {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) {shape : Tree} {childCredit : Nat}
    (child : Recursive.History.Layout weight (.node l x r) shape childCredit)
    {carry fingerWeight : ℝ} (carryNonnegative : 0 ≤ carry) (fingerNonnegative : 0 ≤ fingerWeight)
    (stored : p.lower.top = .leaf shape.mirror (carry + mass weight (.node l x r))) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Recursive.History.Layout weight l a leftCredit ∧ Recursive.History.Layout weight r b rightCredit ∧
      let next := p.downLeft a b (carry + mass weight l) (fingerWeight + mass weight r)
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + leftCredit + rightCredit ≤ 54 + p.potential + childCredit ∧
      next.mass + weight x = p.mass + fingerWeight ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size - r.erase.size - 1) ∧
      (cost : ℝ) ≤ 26 + 24 * Real.logb 2 p.tree.size := by
  obtain ⟨a, b, lc, rc, cost, left, right, trace, nextValid, amortized, balance, rank, worst⟩ :=
    downLeft_within valid child carryNonnegative fingerNonnegative stored
  exact ⟨a, b, lc, rc, cost, left, right, trace.trace, nextValid, amortized, balance, rank, worst⟩

theorem downRight_within {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) {shape : Tree} {childCredit : Nat}
    (child : Recursive.History.Layout weight (.node l x r) shape childCredit)
    {carry fingerWeight : ℝ} (carryNonnegative : 0 ≤ carry) (fingerNonnegative : 0 ≤ fingerWeight)
    (stored : p.upper.top = .leaf shape (carry + mass weight (.node l x r))) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Recursive.History.Layout weight l a leftCredit ∧ Recursive.History.Layout weight r b rightCredit ∧
      let next := p.downRight a b (fingerWeight + mass weight l) (carry + mass weight r)
      Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
        ∀ x, Tree.depth t x ≤ 16 * Tree.depth p.tree x + 64) ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + leftCredit + rightCredit ≤ 54 + p.potential + childCredit ∧
      next.mass + weight x = p.mass + fingerWeight ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size + l.erase.size + 1) ∧
      (cost : ℝ) ≤ 26 + 24 * Real.logb 2 p.tree.size := by
  have positive := Recursive.History.Results.layout_positive child
  have leftNN := HeavyPath.mass_nonnegative (HeavyPath.positive_nonnegative positive.1)
  have rightNN := HeavyPath.mass_nonnegative (HeavyPath.positive_nonnegative positive.2.2)
  obtain ⟨a, b, leftCredit, rightCredit, exposureCost, left, right, exposure, exposureBound, exposureWorst⟩ :=
    Recursive.History.Results.layout_expose_within child
  obtain ⟨cost, trace, bound, nextValid, balance, rank, work⟩ := Interruption.downRight_exposed_within valid stored exposure
    (add_nonneg fingerNonnegative leftNN) (add_nonneg carryNonnegative rightNN)
  rw [Recursive.History.Results.layout_size left] at rank
  refine ⟨a, b, leftCredit, rightCredit, cost, left, right, trace, nextValid, by omega, ?_, rank, ?_⟩
  · simp only [mass] at balance
    linarith
  · have size := Population.Results.upper_payload_size stored
    have positiveSize : 0 < shape.size := by
      rw [Recursive.History.Results.layout_size child]
      simp only [LabelledTree.erase, Tree.size]
      omega
    have logarithm : Real.logb 2 shape.size ≤ Real.logb 2 p.tree.size := by
      apply Real.logb_le_logb_of_le (by norm_num)
      · exact_mod_cast positiveSize
      · exact_mod_cast size
    have stackWorst := Population.Results.lower_push valid
    have workReal : (cost : ℝ) ≤ exposureCost + p.lower.pushCost + 10 := by
      exact_mod_cast work
    linarith

theorem downRight_bounded {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) {shape : Tree} {childCredit : Nat}
    (child : Recursive.History.Layout weight (.node l x r) shape childCredit)
    {carry fingerWeight : ℝ} (carryNonnegative : 0 ≤ carry) (fingerNonnegative : 0 ≤ fingerWeight)
    (stored : p.upper.top = .leaf shape (carry + mass weight (.node l x r))) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Recursive.History.Layout weight l a leftCredit ∧ Recursive.History.Layout weight r b rightCredit ∧
      let next := p.downRight a b (fingerWeight + mass weight l) (carry + mass weight r)
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + leftCredit + rightCredit ≤ 54 + p.potential + childCredit ∧
      next.mass + weight x = p.mass + fingerWeight ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size + l.erase.size + 1) ∧
      (cost : ℝ) ≤ 26 + 24 * Real.logb 2 p.tree.size := by
  obtain ⟨a, b, lc, rc, cost, left, right, trace, nextValid, amortized, balance, rank, worst⟩ :=
    downRight_within valid child carryNonnegative fingerNonnegative stored
  exact ⟨a, b, lc, rc, cost, left, right, trace.trace, nextValid, amortized, balance, rank, worst⟩

theorem downLeft {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) {shape : Tree} {childCredit : Nat}
    (child : Recursive.History.Layout weight (.node l x r) shape childCredit)
    {carry fingerWeight : ℝ} (carryNonnegative : 0 ≤ carry) (fingerNonnegative : 0 ≤ fingerWeight)
    (stored : p.lower.top = .leaf shape.mirror (carry + mass weight (.node l x r))) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Recursive.History.Layout weight l a leftCredit ∧ Recursive.History.Layout weight r b rightCredit ∧
      let next := p.downLeft a b (carry + mass weight l) (fingerWeight + mass weight r)
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + leftCredit + rightCredit ≤ 54 + p.potential + childCredit ∧
      next.mass + weight x = p.mass + fingerWeight ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size - r.erase.size - 1) := by
  obtain ⟨a, b, lc, rc, cost, left, right, trace, nextValid, amortized, balance, rank, _⟩ :=
    downLeft_bounded valid child carryNonnegative fingerNonnegative stored
  exact ⟨a, b, lc, rc, cost, left, right, trace, nextValid, amortized, balance, rank⟩

theorem downRight {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) {shape : Tree} {childCredit : Nat}
    (child : Recursive.History.Layout weight (.node l x r) shape childCredit)
    {carry fingerWeight : ℝ} (carryNonnegative : 0 ≤ carry) (fingerNonnegative : 0 ≤ fingerWeight)
    (stored : p.upper.top = .leaf shape (carry + mass weight (.node l x r))) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Recursive.History.Layout weight l a leftCredit ∧ Recursive.History.Layout weight r b rightCredit ∧
      let next := p.downRight a b (fingerWeight + mass weight l) (carry + mass weight r)
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + leftCredit + rightCredit ≤ 54 + p.potential + childCredit ∧
      next.mass + weight x = p.mass + fingerWeight ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size + l.erase.size + 1) := by
  obtain ⟨a, b, lc, rc, cost, left, right, trace, nextValid, amortized, balance, rank, _⟩ :=
    downRight_bounded valid child carryNonnegative fingerNonnegative stored
  exact ⟨a, b, lc, rc, cost, left, right, trace, nextValid, amortized, balance, rank⟩

end RotationBST.HeavyPath.Finger.Transfer.History
