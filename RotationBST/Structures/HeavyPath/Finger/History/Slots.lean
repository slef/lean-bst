module

public import RotationBST.Structures.HeavyPath.Finger.History.Definitions.Abstract
public import RotationBST.Structures.HeavyPath.Recursive.History.Abstract
public import RotationBST.Structures.HeavyPath.Finger.Slots
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History
open Paired Recursive LabelledCursor PopTart PopTart.WeightedTree Recursive.History

theorem sideSlots_mass {α : Type} (weight : α → ℝ) (boundary : LabelledTree α)
    (shape : Tree) (carry : ℝ) (es : List (Entry α)) :
    ((sideSlots weight boundary shape carry es).map Prod.snd).sum =
      carry + HeavyPath.mass weight boundary + (es.map (fun e => frameMass weight e.source)).sum := by
  induction es generalizing carry with
  | nil => simp [sideSlots]
  | cons e es ih =>
    simp only [sideSlots, List.map_cons, List.sum_cons, ih]
    cases h : e.source <;> simp only [framePayload, frameKey, frameMass] <;> ring

theorem sideSlots_span {α : Type} (weight : α → ℝ) (boundary : LabelledTree α)
    (shape : Tree) (carry : ℝ) (es : List (Entry α)) :
    fringeSpan (sideSlots weight boundary shape carry es) =
      (es.map (fun e => e.shape.size + 1)).sum + shape.size + 1 := by
  induction es generalizing carry with
  | nil => simp [sideSlots, fringeSpan]
  | cons e es ih =>
    change e.shape.size + 1 + fringeSpan (sideSlots weight boundary shape (weight (frameKey e.source)) es) = _
    rw [ih]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sideSlots_lengths {α : Type} {weight : α → ℝ} {boundary : LabelledTree α}
    {shape : Tree} {credit : Nat} (boundaryLayout : Recursive.History.Layout weight boundary shape credit)
    (carry : ℝ) {es : List (Entry α)}
    (children : ∀ e ∈ es, Recursive.History.Layout weight (framePayload e.source) e.shape e.credit) :
    fringeSpan (sideSlots weight boundary shape carry es) =
        (es.flatMap Entry.lowerBlock ++ boundary.inorder).length + 1 ∧
    fringeSpan (sideSlots weight boundary shape carry es) =
        (boundary.inorder ++ es.reverse.flatMap Entry.upperBlock).length + 1 := by
  have lower : es.map (fun e => e.shape.size + 1) = es.map (fun e => e.lowerBlock.length) := by
    apply List.map_congr_left
    intro e he
    rw [layout_size (children e he)]
    exact (block_length e.source).1.symm
  have upper : es.map (fun e => e.shape.size + 1) = es.map (fun e => e.upperBlock.length) := by
    apply List.map_congr_left
    intro e he
    rw [layout_size (children e he)]
    exact (block_length e.source).2.symm
  have boundarySize : shape.size = boundary.inorder.length := by
    rw [layout_size boundaryLayout, Representation.Bridge.inorder_length]
  constructor
  · simp only [List.length_append, List.length_flatMap]
    rw [sideSlots_span, lower, boundarySize]
  · simp only [List.length_append, List.length_flatMap, List.map_reverse, List.sum_reverse]
    rw [sideSlots_span, upper, boundarySize]
    omega

theorem context_inorder {α : Type} {cs : List (Frame α)} {es : List (Entry α)}
    (context : es.map Entry.source = cs) (focus : LabelledTree α) :
    (plug cs focus).inorder = (Recursive.History.lower es).flatMap Entry.lowerBlock ++
      focus.inorder ++ (Recursive.History.upper es).flatMap Entry.upperBlock := by
  have original := Recursive.context_inorder cs focus
  rw [← context, ← lower_sources, ← upper_sources] at original
  change (plug cs focus).inorder = (Recursive.History.lower es).flatMap (fun e => Recursive.lowerBlock e.source) ++
    focus.inorder ++ (Recursive.History.upper es).flatMap (fun e => Recursive.upperBlock e.source)
  simpa only [context, List.flatMap_map, Function.comp_def] using original

theorem frame_positive {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α} {s : State α}
    (valid : Valid weight cs left key right s) {e : Entry α} (member : e ∈ s.ancestors) :
    Positive weight (framePayload e.source) ∧ 0 < weight (frameKey e.source) := by
  have source : e.source ∈ cs := by rw [← valid.context]; exact List.mem_map_of_mem member
  exact ⟨payload_positive cs _ valid.positive source, context_key_positive cs _ valid.positive source⟩

end RotationBST.HeavyPath.Finger.History
