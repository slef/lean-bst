module

public import RotationBST.Structures.HeavyPath.Recursive.History.Accounting
public import RotationBST.Structures.PopTart.Chocolate.PotentialBound
public import RotationBST.Structures.PopTart.Mirror.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History
open Paired LabelledCursor PopTart

theorem split_lengths {α : Type} (es : List (Entry α)) :
    (lower es).length + (upper es).length = es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      cases h : e.source <;> simp only [lower, upper, h, List.length_append,
        List.length_cons, List.length_nil] <;> omega

/-- Active and frozen path credit is charged only to path separators; the
payloads' own credits are accounted for separately by the recursive layout. -/
theorem path_potential_bound {α : Type} {weight : α → ℝ} {es : List (Entry α)} {p : Stacks}
    (valid : PathValid weight es p) : p.potential ≤ 20 * es.length := by
  have lo := congrArg List.length valid.lower
  have hi := congrArg List.length valid.upper
  simp only [WeightedTree.mirror_fringe, List.length_reverse, List.length_map,
    List.length_append, List.length_cons, List.length_nil] at lo hi
  have left := Chocolate.layer_potential_fringe p.lower
  have right := Chocolate.layer_potential_fringe p.upper
  rw [lo] at left
  rw [hi] at right
  have lengths := split_lengths es
  simp only [Stacks.potential]
  omega

theorem entry_credit_sum {α : Type} (es : List (Entry α)) (factor : Nat)
    (bounds : ∀ e ∈ es, e.credit ≤ factor * (framePayload e.source).erase.size) :
    (es.map Entry.credit).sum ≤ factor * (es.map (fun e => (framePayload e.source).erase.size)).sum := by
  induction es with
  | nil => simp
  | cons e es ih =>
      have head := bounds e (by simp)
      have tail := ih (fun f member => bounds f (by simp [member]))
      simp only [List.map_cons, List.sum_cons, Nat.mul_add]
      omega

/-- Every valid recursive history has linear stored credit, regardless of
how many operations produced it. Frozen layers retain their credit in this sum. -/
theorem layout_potential_bound {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    {shape : Tree} {credit : Nat} (layout : Layout weight t shape credit) :
    credit ≤ 20 * t.erase.size := by
  induction layout with
  | nil => exact le_rfl
  | @path t es p positive nonempty context valid children ih =>
      have outer := path_potential_bound valid
      have inner := entry_credit_sum es 20 ih
      obtain ⟨endpoint, focus⟩ := HeavyPath.Results.extract_terminal positive nonempty
      have partition := context_size α (extract weight t).context (extract weight t).focus
      change (extract weight t).tree.erase.size = _ at partition
      rw [HeavyPath.Results.extract_tree, focus, ← context] at partition
      simp only [LabelledTree.erase, Tree.size, List.length_map, List.map_map,
        Function.comp_def] at partition
      omega

end RotationBST.HeavyPath.Recursive.History
