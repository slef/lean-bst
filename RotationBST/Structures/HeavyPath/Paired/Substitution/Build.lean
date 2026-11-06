module

public import RotationBST.Structures.HeavyPath.Paired.Substitution.Push
public import RotationBST.Structures.HeavyPath.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Paired
open PopTart PopTart.Chocolate LabelledCursor

/-- All ancestors are consumed in one physical trace. The finger stays on
the endpoint between consecutive pushes and ends at the root of the pair. -/
theorem buildWith_trace {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree) (cs : List (Frame α)) (p : Stacks)
    (ds : List Pointer.Frame) :
    Pointer.Trace ⟨p.tree, cs.map (replaceFrame payload) ++ ds⟩
      ⟨(Stacks.buildWith weight payload cs p).tree, ds⟩ (Stacks.buildWithCost weight payload cs p) := by
  induction cs generalizing p with
  | nil => exact .refl
  | cons frame cs ih =>
    exact (pushWith_trace weight payload frame p (cs.map (replaceFrame payload) ++ ds)).append (ih (p.pushWith weight payload frame))

theorem buildWith_valid {α : Type} {weight : α → ℝ} (payload : LabelledTree α → Tree) (cs : List (Frame α)) {p : Stacks}
    (valid : p.Valid) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    (Stacks.buildWith weight payload cs p).Valid := by
  induction cs generalizing p with
  | nil => exact valid
  | cons frame cs ih =>
    exact ih (pushWith_valid payload valid (nonnegative frame (by simp)))
      (by intro f hf; exact nonnegative f (by simp [hf]))

theorem buildWith_amortized {α : Type} {weight : α → ℝ} (payload : LabelledTree α → Tree) (cs : List (Frame α)) {p : Stacks}
    (valid : p.Valid) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    Stacks.buildWithCost weight payload cs p + (Stacks.buildWith weight payload cs p).potential ≤ 23 * cs.length + p.potential := by
  induction cs generalizing p with
  | nil => simp [Stacks.buildWithCost, Stacks.buildWith]
  | cons frame cs ih =>
    have first := pushWith_amortized payload valid (nonnegative frame (by simp))
    have later := ih (pushWith_valid payload valid (nonnegative frame (by simp)))
      (by intro f hf; exact nonnegative f (by simp [hf]))
    simp only [Stacks.buildWithCost, Stacks.buildWith, List.length_cons]
    omega

theorem buildWith_mass {α : Type} {weight : α → ℝ} (payload : LabelledTree α → Tree) (cs : List (Frame α)) {p : Stacks}
    (valid : p.Valid) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    (Stacks.buildWith weight payload cs p).mass = p.mass + (cs.map (frameMass weight)).sum := by
  induction cs generalizing p with
  | nil => simp [Stacks.buildWith]
  | cons frame cs ih =>
    rw [Stacks.buildWith, ih (pushWith_valid payload valid (nonnegative frame (by simp)))
      (by intro f hf; exact nonnegative f (by simp [hf])),
      pushWith_mass payload valid (nonnegative frame (by simp))]
    simp [add_assoc]

/-- The final root rank includes the actual sizes of the replacement payloads. -/
theorem buildWith_lower_size {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree) (cs : List (Frame α)) (p : Stacks) :
    (Stacks.buildWith weight payload cs p).lower.decode.tree.size =
      p.lower.decode.tree.size + Pointer.offset (cs.map (replaceFrame payload)) := by
  induction cs generalizing p with
  | nil => simp [Stacks.buildWith, Pointer.offset]
  | cons frame cs ih =>
    rw [Stacks.buildWith, ih, pushWith_lower_size]
    cases frame <;> simp [Pointer.offset, replaceFrame, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end RotationBST.HeavyPath.Paired
