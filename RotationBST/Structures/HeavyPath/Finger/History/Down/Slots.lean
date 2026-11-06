module

public import RotationBST.Structures.HeavyPath.Finger.History.Slots
public import RotationBST.Structures.PopTart.Chocolate.Top.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Down
open Paired Recursive LabelledCursor PopTart PopTart.WeightedTree PopTart.Chocolate Recursive.History

/-- The final payload carries precisely the nearest separator's weight.
The preceding physical slots are independent of this payload's shape. -/
theorem sideSlots_end {α : Type} {weight : α → ℝ} {es : List (Entry α)}
    (positive : ∀ e ∈ es, 0 < weight (frameKey e.source)) {carry : ℝ} (nonnegative : 0 ≤ carry) :
    ∃ (before : List (Tree × ℝ)) (lastCarry : ℝ), 0 ≤ lastCarry ∧
      ∀ boundary shape, sideSlots weight boundary shape carry es =
        before ++ [(shape, lastCarry + HeavyPath.mass weight boundary)] := by
  induction es generalizing carry with
  | nil => exact ⟨[], carry, nonnegative, fun _ _ => rfl⟩
  | cons e es ih =>
    obtain ⟨before, lastCarry, lastNonnegative, ending⟩ :=
      ih (fun f hf => positive f (by simp [hf])) (positive e (by simp)).le
    refine ⟨(e.shape, carry + HeavyPath.mass weight (framePayload e.source)) :: before,
      lastCarry, lastNonnegative, ?_⟩
    intro boundary shape
    simp only [sideSlots, ending, List.cons_append]

theorem sideSlots_append {α : Type} (weight : α → ℝ) (boundary : LabelledTree α)
    (shape : Tree) (carry : ℝ) (es : List (Entry α)) (e : Entry α) :
    sideSlots weight boundary shape carry (es ++ [e]) =
      sideSlots weight (framePayload e.source) e.shape carry es ++
        [(shape, weight (frameKey e.source) + HeavyPath.mass weight boundary)] := by
  induction es generalizing carry with
  | nil => rfl
  | cons f es ih => simp only [List.cons_append, sideSlots, ih]

theorem top_front {stack : Layer} (valid : stack.Valid 0) {shape : Tree} {charge : ℝ}
    {after : List (Tree × ℝ)} (fringe : stack.decode.fringe = (shape, charge) :: after) :
    stack.top = .leaf shape charge := by
  have perfect := (Chocolate.Top.Results.top_valid valid).1
  cases top : stack.top with
  | leaf t w =>
    have head : ∃ rest, stack.decode.fringe = (t, w) :: rest := by
      rw [Chocolate.Top.Results.decode_top, top]
      cases stack.topTail with
      | none => exact ⟨[], rfl⟩
      | some tail => exact ⟨tail.fringe, rfl⟩
    obtain ⟨rest, head⟩ := head
    have eq := (List.cons.inj (head.symm.trans fringe)).1
    rcases Prod.mk.inj eq with ⟨rfl, rfl⟩
    rfl
  | node a b => rw [top] at perfect; cases perfect

theorem top_back {stack : Layer} (valid : stack.Valid 0) {shape : Tree} {charge : ℝ}
    {before : List (Tree × ℝ)} (fringe : stack.decode.mirror.fringe = before ++ [(shape, charge)]) :
    stack.top = .leaf shape.mirror charge := by
  have raw := WeightedTree.mirror_fringe stack.decode.mirror
  rw [WeightedTree.mirror_mirror, fringe] at raw
  have front : stack.decode.fringe = (shape.mirror, charge) ::
      (before.map (fun e => (e.1.mirror, e.2))).reverse := by
    simpa only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append] using raw
  exact top_front valid front

end RotationBST.HeavyPath.Finger.History.Down
