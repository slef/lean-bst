module

public import RotationBST.Structures.HeavyPath.Paired.Substitution.Definitions.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Abstract
public import RotationBST.Structures.PopTart.Mirror.Abstract
public import RotationBST.Models.Pointer.Navigation
public import RotationBST.Models.Pointer.Keys
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Paired
open PopTart PopTart.Chocolate LabelledCursor

private theorem push_size (stack : Layer) (new : WeightedTree) :
    (stack.push new).decode.tree.size = new.tree.size + stack.decode.tree.size + 1 := by
  obtain ⟨_, _, rotations⟩ := (Chocolate.Results.push_trace stack new).rotations
  simpa only [Pointer.Config.tree, Pointer.plug, Tree.size, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using rotations.size_eq.symm

private theorem push_nonempty (stack : Layer) (new : WeightedTree) :
    (stack.push new).decode.tree ≠ .nil := by
  intro empty
  have size := push_size stack new
  rw [empty, Tree.size] at size
  omega

/-- The next path separator is already present above the endpoint. Raising
the endpoint exposes the push boundary, so no insertion is assumed free. -/
theorem pushWith_trace {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree) (frame : Frame α) (p : Stacks)
    (cs : List Pointer.Frame) :
    Pointer.Trace ⟨p.tree, replaceFrame payload frame :: cs⟩ ⟨(p.pushWith weight payload frame).tree, cs⟩ (p.pushCost frame) := by
  cases frame with
  | left x r =>
    let new : WeightedTree := .leaf (payload r).mirror (weight x + HeavyPath.mass weight r)
    have trace := (Chocolate.Results.push_trace p.upper new).mirror
    have nonempty : (p.upper.push new).decode.tree.mirror ≠ .nil := by
      intro eq
      have eq' := congrArg Tree.mirror eq
      simp only [Tree.mirror_mirror, Tree.mirror] at eq'
      exact push_nonempty p.upper new eq'
    have embedded := trace.inContext (by intro h; cases h) nonempty [.right p.lower.decode.tree]
    have contextual := embedded.under cs
    have result := Pointer.Trace.step (Pointer.Step.rotateLeftChild) contextual
    convert result using 1 <;> simp [Stacks.tree, Stacks.pushWith, Stacks.pushCost, new,
      Pointer.Config.under, Pointer.plug, replaceFrame, WeightedTree.tree,
      WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree, Nat.add_comm]
    omega
  | right l x =>
    let new : WeightedTree := .leaf (payload l) (HeavyPath.mass weight l + weight x)
    have trace := Chocolate.Results.push_trace p.lower new
    have embedded := trace.inContext (by intro h; cases h) (push_nonempty p.lower new)
      [.left p.upper.decode.tree.mirror]
    have contextual := embedded.under cs
    have result := Pointer.Trace.step (Pointer.Step.rotateRightChild) contextual
    convert result using 1 <;> simp [Stacks.tree, Stacks.pushWith, Stacks.pushCost, new, Pointer.Config.under,
      Pointer.plug, replaceFrame, WeightedTree.tree, WeightedTree.skeleton,
      Pointer.Lazy.Skeleton.tree, Nat.add_comm]
    omega

theorem pushWith_valid {α : Type} {weight : α → ℝ} {frame : Frame α} {p : Stacks}
    (payload : LabelledTree α → Tree) (valid : p.Valid) (nonnegative : 0 ≤ frameMass weight frame) : (p.pushWith weight payload frame).Valid := by
  cases frame with
  | left x r =>
    exact ⟨valid.1, (Chocolate.Results.push valid.2 (.leaf _ _) nonnegative []).1⟩
  | right l x =>
    exact ⟨(Chocolate.Results.push valid.1 (.leaf _ _) nonnegative []).1, valid.2⟩

theorem pushWith_amortized {α : Type} {weight : α → ℝ} {frame : Frame α} {p : Stacks}
    (payload : LabelledTree α → Tree) (valid : p.Valid) (nonnegative : 0 ≤ frameMass weight frame) :
    p.pushCost frame + (p.pushWith weight payload frame).potential ≤ 23 + p.potential := by
  cases frame with
  | left x r =>
    have bound := (Chocolate.Results.push valid.2 (.leaf (payload r).mirror _) nonnegative []).2.2.2.2
    simp only [frameMass] at bound
    simp only [Stacks.pushCost, Stacks.pushWith, Stacks.potential]
    omega
  | right l x =>
    have bound := (Chocolate.Results.push valid.1 (.leaf (payload l) _) nonnegative []).2.2.2.2
    simp only [frameMass] at bound
    simp only [Stacks.pushCost, Stacks.pushWith, Stacks.potential]
    omega

theorem pushWith_mass {α : Type} {weight : α → ℝ} {frame : Frame α} {p : Stacks}
    (payload : LabelledTree α → Tree) (valid : p.Valid) (nonnegative : 0 ≤ frameMass weight frame) :
    (p.pushWith weight payload frame).mass = p.mass + frameMass weight frame := by
  cases frame with
  | left x r =>
    have eq := (Chocolate.Results.push valid.2 (.leaf (payload r).mirror _) nonnegative []).2.2.1
    simp only [Stacks.pushWith, Stacks.mass, WeightedTree.mass, frameMass] at *
    rw [eq]
    ring
  | right l x =>
    have eq := (Chocolate.Results.push valid.1 (.leaf (payload l) _) nonnegative []).2.2.1
    simp only [Stacks.pushWith, Stacks.mass, WeightedTree.mass, frameMass] at *
    rw [eq]
    ring

theorem pushWith_lower_size {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree) (frame : Frame α) (p : Stacks) :
    (p.pushWith weight payload frame).lower.decode.tree.size =
      p.lower.decode.tree.size + Pointer.offset [replaceFrame payload frame] := by
  cases frame with
  | left x r => simp [Stacks.pushWith, Pointer.offset, replaceFrame]
  | right l x =>
    change (p.lower.push (.leaf (payload l) (HeavyPath.mass weight l + weight x))).decode.tree.size =
      p.lower.decode.tree.size + (0 + (payload l).size + 1)
    rw [push_size]
    change (payload l).size + p.lower.decode.tree.size + 1 = p.lower.decode.tree.size + (0 + (payload l).size + 1)
    omega

end RotationBST.HeavyPath.Paired
