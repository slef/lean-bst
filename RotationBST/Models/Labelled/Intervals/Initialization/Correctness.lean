module

public import RotationBST.Models.Labelled.Intervals.Initialization.Operational
public import RotationBST.Models.Labelled.Intervals.Representation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.IntervalMetadata.Initialization
open Pointer

/-- The supplied universe size is an explicit scalar input. Initialization
halts at the original root, sets every interval field, and leaves nonexisting
keys unchanged. All pointer, word-access, and null-link work is included. -/
theorem complete (tree : Tree) (n : Nat) (size : n = tree.size) (fields : Nat → Bounds) :
    ∃ final cost, Run (initial tree n fields) final cost ∧ tick final = none ∧
      final.cursor = ⟨tree, []⟩ ∧ Metadata.label final.fields tree 0 = label tree 0 ∧
      cost ≤ 8 * n ∧ (∀ x, n ≤ x → final.fields x = fields x) := by
  subst n
  by_cases empty : tree = .nil
  · subst tree
    exact ⟨initial .nil 0 fields, 0, .refl, rfl, rfl, rfl, Nat.le_refl _, fun _ _ => rfl⟩
  · obtain ⟨pending, run⟩ := traversal tree empty [] fields
    refine ⟨⟨⟨tree, []⟩, populate tree 0 fields, pending, .up⟩, work tree, ?_, ?_, rfl,
      populate_label tree 0 fields, work_bound tree, ?_⟩
    · simpa only [initial, offset, Nat.zero_add] using run
    · cases tree <;> rfl
    · intro x outside
      exact populate_outside tree 0 fields x (Or.inr (by simpa only [Nat.zero_add] using outside))

/-- Arbitrary old bounded word values are permitted. Every execution prefix
keeps both pending registers and all node fields within the same word limit. -/
theorem prefix_bounded (tree : Tree) (n limit : Nat) (size : n = tree.size) (fits : n ≤ limit)
    (fields : Nat → Bounds) (oldWords : ∀ x, (fields x).low ≤ limit ∧ (fields x).high ≤ limit)
    {final : State} {cost : Nat} (run : Run (initial tree n fields) final cost) : final.Bounded limit := by
  apply run.bounded
  exact ⟨by simpa only [initial, Config.tree, plug, ← size] using fits, Nat.zero_le _, fits, oldWords⟩

/-- Reading the initialized fields at any existing cursor gives a correct
local routing view. No recursive size/offset computation occurs in the read. -/
theorem read_view (fields : Nat → Bounds) (cursor : Config) (key : Nat) (atKey : cursor.key? = some key)
    (initialized : Metadata.label fields cursor.tree 0 = label cursor.tree 0) :
    (Routing.View.mk (fields key).low key (fields key).high).Valid cursor := by
  let view : Routing.View := ⟨offset cursor.context, key, offset cursor.context + cursor.focus.size⟩
  have valid : view.Valid cursor := ⟨rfl, atKey, rfl⟩
  have atNode := view_at view cursor valid
  rw [← initialized] at atNode
  have value := Metadata.at_payload fields cursor.tree 0 key (Bounds.mk view.low view.high) atNode
  rw [← value]
  exact valid

end RotationBST.IntervalMetadata.Initialization
