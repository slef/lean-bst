module

public import RotationBST.Structures.HeavyPath.Finger.History.Down.Slots
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Up
open Paired Recursive LabelledCursor PopTart PopTart.Chocolate PopTart.WeightedTree Recursive.History

theorem split_context {α : Type} {es : List (Entry α)} {f : Frame α} {cs : List (Frame α)}
    (context : es.map Entry.source = f :: cs) :
    ∃ e rest, es = e :: rest ∧ e.source = f ∧ rest.map Entry.source = cs := by
  cases es with
  | nil => cases context
  | cons e es => exact ⟨e, es, rfl, (List.cons.inj context).1, (List.cons.inj context).2⟩

theorem sideSlots_nonempty {α : Type} (weight : α → ℝ) (boundary : LabelledTree α)
    (shape : Tree) (carry : ℝ) (es : List (Entry α)) : sideSlots weight boundary shape carry es ≠ [] := by
  cases es <;> simp [sideSlots]

theorem raw_of_back {tree : WeightedTree} {old : Tree} {oldCharge : ℝ} {before : List (Tree × ℝ)}
    (fringe : tree.mirror.fringe = before ++ [(old, oldCharge)]) :
    tree.fringe = (old.mirror, oldCharge) :: (before.map reflectSlot).reverse := by
  change tree.fringe = (old.mirror, oldCharge) :: (before.map (fun e => (e.1.mirror, e.2))).reverse
  have raw := mirror_fringe tree.mirror
  rw [mirror_mirror, fringe] at raw
  simpa only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append] using raw

theorem mirror_of_raw {tree : WeightedTree} {entries : List (Tree × ℝ)}
    (fringe : tree.fringe = (entries.map reflectSlot).reverse) : tree.mirror.fringe = entries := by
  rw [mirror_fringe, fringe]
  change (((entries.map reflectSlot).reverse).map reflectSlot).reverse = entries
  simp only [List.map_reverse, List.map_map, Function.comp_def, reflectSlot_involutive, List.reverse_reverse]
  exact List.map_id entries

theorem replace_front {stack : Layer} {old shape : Tree} {oldCharge charge : ℝ}
    (stored : stack.top = .leaf old oldCharge) {after : List (Tree × ℝ)}
    (fringe : stack.decode.fringe = (old, oldCharge) :: after) :
    (stack.replaceTop (.leaf shape charge)).decode.fringe = (shape, charge) :: after := by
  rw [decode_top, stored] at fringe
  rw [replaceTop_decode]
  cases tail : stack.topTail with
  | none =>
    rw [tail] at fringe
    have ending : [] = after := (List.cons.inj fringe).2
    rw [← ending]
    rfl
  | some suffix =>
    rw [tail] at fringe
    have ending : suffix.fringe = after := (List.cons.inj fringe).2
    rw [← ending]
    rfl

theorem replace_back {stack : Layer} {old shape : Tree} {oldCharge charge : ℝ}
    (stored : stack.top = .leaf old.mirror oldCharge) {before : List (Tree × ℝ)}
    (fringe : stack.decode.mirror.fringe = before ++ [(old, oldCharge)]) :
    (stack.replaceTop (.leaf shape.mirror charge)).decode.mirror.fringe = before ++ [(shape, charge)] := by
  apply mirror_of_raw
  have raw := replace_front (shape := shape.mirror) (charge := charge) stored (raw_of_back fringe)
  simpa only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, reflectSlot] using raw

end RotationBST.HeavyPath.Finger.History.Up
