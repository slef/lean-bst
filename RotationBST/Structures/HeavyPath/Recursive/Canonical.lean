module

public import RotationBST.Structures.HeavyPath.Recursive.Preservation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive
open Paired LabelledCursor

/-- The full recursive layout is canonical. The auxiliary payload function
matters only at actual off-path occurrences, where recursive uniqueness fixes
its value. Empty and repeated-shaped payloads cause no ambiguity. -/
theorem layout_unique {α : Type} {weight : α → ℝ} {t : LabelledTree α} {first second : Tree}
    (left : Layout weight t first) (right : Layout weight t second) : first = second := by
  induction left generalizing second with
  | nil =>
    cases right with
    | nil => rfl
    | path positive nonempty terminal children => exact False.elim (nonempty rfl)
  | @path t payload positive nonempty terminal children ih =>
    cases right with
    | nil => exact False.elim (nonempty rfl)
    | @path t other positive' nonempty' terminal' children' =>
      congr 1
      apply buildWith_congr
      intro frame mem
      exact ih frame mem (children' frame mem)

theorem rebuildFuel_eq {α : Type} {weight : α → ℝ} (fuel : Nat) {t : LabelledTree α}
    (positive : Positive weight t) (enough : t.erase.size ≤ fuel) :
    rebuildFuel weight fuel t = rebuild weight t :=
  layout_unique (rebuildFuel_layout fuel positive enough) (rebuild_layout positive)

/-- The public constructor satisfies the recursive paired-path equation with
the public constructor itself in every off-path payload. Fuel is an internal
termination device and has no effect on this equation. -/
theorem rebuild_eq {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) :
    rebuild weight t =
      (Stacks.buildWith weight (rebuild weight) (extract weight t).context Stacks.empty).tree := by
  obtain ⟨endpoint, payload, focus, shape, valid, mass, children⟩ :=
    layout_unfold (rebuild_layout positive) nonempty
  rw [shape]
  congr 1
  apply buildWith_congr
  intro frame mem
  exact layout_unique (children frame mem) (rebuild_layout (extract_payload_positive positive mem))

/-- Recursively restructuring the off-path payloads does not change the
endpoint's original inorder rank at the new root. -/
theorem rebuild_root_key {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) :
    (Pointer.Config.mk (rebuild weight t) []).key? = (extract weight t).erase.key? := by
  obtain ⟨endpoint, focus⟩ := HeavyPath.Results.extract_terminal positive nonempty
  rw [rebuild_eq positive nonempty]
  simp only [Stacks.tree, Pointer.Config.key?, Pointer.offset, Config.erase,
    focus, LabelledTree.erase, Tree.size, Nat.zero_add, Nat.add_zero]
  rw [buildWith_lower_size, replaced_offset (rebuild weight) _
    (by intro frame mem; exact rebuild_size (extract_payload_positive positive mem))]
  change some (0 + _) = _
  simp only [Nat.zero_add]

theorem rebuild_pair {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) :
    let q := extract weight t
    let p := Stacks.buildWith weight (rebuild weight) q.context Stacks.empty
    ∃ endpoint, q.focus = .node .nil endpoint .nil ∧ rebuild weight t = p.tree ∧
      p.Valid ∧ weight endpoint + p.mass = HeavyPath.mass weight t ∧
      p.lower.decode.fringe = (lowerSlotsWith weight (rebuild weight) q.context).reverse ++ [(.nil, 0)] ∧
      p.upper.decode.mirror.fringe = [(.nil, 0)] ++ upperSlotsWith weight (rebuild weight) q.context := by
  dsimp only
  obtain ⟨endpoint, focus⟩ := HeavyPath.Results.extract_terminal positive nonempty
  have charges : ∀ frame ∈ (extract weight t).context, 0 ≤ frameMass weight frame := by
    intro frame mem
    exact ((HeavyPath.Results.extract_positive positive).2 frame mem).le
  have fringe := buildWith_fringe (rebuild weight) (extract weight t).context empty_valid charges
  refine ⟨endpoint, focus, rebuild_eq positive nonempty,
    buildWith_valid (rebuild weight) _ empty_valid charges, ?_, fringe⟩
  rw [buildWith_mass (rebuild weight) _ empty_valid charges]
  have partition := HeavyPath.Results.extract_mass weight t
  rw [focus] at partition
  simpa only [HeavyPath.mass, zero_add, add_zero, Stacks.mass, Stacks.empty,
    PopTart.Chocolate.Layer.decode, PopTart.Chocolate.Regulars.attach,
    PopTart.Chocolate.Icing.decode, PopTart.WeightedTree.mass] using partition.symm

end RotationBST.HeavyPath.Recursive
