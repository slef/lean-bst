module

public import RotationBST.Structures.HeavyPath.Recursive.Subtrees
public import RotationBST.Structures.HeavyPath.Paired.Substitution.Abstract
public import RotationBST.Structures.HeavyPath.Paired.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive
open Paired LabelledCursor

/-- The explicit fuel bound never leaves a nonempty subtree unrepresented:
every recursive payload is smaller than the current original tree. -/
theorem rebuildFuel_layout {α : Type} {weight : α → ℝ} (fuel : Nat) {t : LabelledTree α}
    (positive : Positive weight t) (enough : t.erase.size ≤ fuel) :
    Layout weight t (rebuildFuel weight fuel t) := by
  induction fuel generalizing t with
  | zero =>
    cases t with
    | nil => exact .nil
    | node l x r => simp only [LabelledTree.erase, Tree.size] at enough; omega
  | succ fuel ih =>
    cases t with
    | nil => exact .nil
    | node l x r =>
      have nonempty : LabelledTree.node l x r ≠ .nil := by intro h; cases h
      obtain ⟨endpoint, focus⟩ := HeavyPath.Results.extract_terminal positive nonempty
      rw [rebuildFuel, focus]
      apply Layout.path positive nonempty ⟨endpoint, focus⟩
      intro frame mem
      apply ih (extract_payload_positive positive mem)
      have smaller := extract_payload_size weight (.node l x r) mem
      omega

theorem rebuild_layout {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) : Layout weight t (rebuild weight t) :=
  rebuildFuel_layout t.erase.size positive le_rfl

/-- Each nonempty layout has valid Chocolate metadata, unchanged analysis
mass, and recursively represented off-path children. -/
theorem layout_unfold {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree}
    (layout : Layout weight t shape) (nonempty : t ≠ .nil) :
    ∃ endpoint payload,
      (extract weight t).focus = .node .nil endpoint .nil ∧
      shape = (Stacks.buildWith weight payload (extract weight t).context Stacks.empty).tree ∧
      (Stacks.buildWith weight payload (extract weight t).context Stacks.empty).Valid ∧
      weight endpoint + (Stacks.buildWith weight payload (extract weight t).context Stacks.empty).mass =
        HeavyPath.mass weight t ∧
      ∀ frame ∈ (extract weight t).context,
        Layout weight (framePayload frame) (payload (framePayload frame)) := by
  cases layout with
  | nil => exact False.elim (nonempty rfl)
  | @path t payload positive sourceNonempty terminal children =>
    obtain ⟨endpoint, focus⟩ := terminal
    have charges : ∀ frame ∈ (extract weight t).context, 0 ≤ frameMass weight frame := by
      intro frame mem
      exact ((HeavyPath.Results.extract_positive positive).2 frame mem).le
    refine ⟨endpoint, payload, focus, rfl, buildWith_valid payload _ empty_valid charges, ?_, children⟩
    rw [buildWith_mass payload _ empty_valid charges]
    have partition := HeavyPath.Results.extract_mass weight t
    rw [focus] at partition
    simpa only [HeavyPath.mass, zero_add, add_zero, Stacks.mass, Stacks.empty,
      PopTart.Chocolate.Layer.decode, PopTart.Chocolate.Regulars.attach,
      PopTart.Chocolate.Icing.decode, PopTart.WeightedTree.mass] using partition.symm

end RotationBST.HeavyPath.Recursive
